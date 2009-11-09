#! /usr/bin/perl

##--------------------------------------------------------------------##
##--- Massif's results printer                                     ---##
##--------------------------------------------------------------------##

#  This file is based on the original ms_print.pl.in, 
#  Copyright (C) 2007-2007 Nicholas Nethercote
#     njn@valgrind.org
#
#  The "massif_grapher" changes are 
#  Copyright (C) 2009 Murray Cumming
#     murrayc@openismus.com
#
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License as
#  published by the Free Software Foundation; either version 2 of the
#  License, or (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful, but
#  WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#  General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
#  02111-1307, USA.
#
#  The GNU General Public License is contained in the file COPYING.

use warnings;
use strict;

# This it the TODO package on Ubuntu.
use GD::Graph::area;
use GD::Graph::Data;


#----------------------------------------------------------------------------
# Global variables, main data structures
#----------------------------------------------------------------------------

# Command line of profiled program.
my $cmd;

# Time unit used in profile.
my $time_unit;

# Threshold dictating what percentage an entry must represent for us to
# bother showing it.
my $threshold = 1.0;

# Input file name
my $input_file = undef;

# Tmp file name.
my $tmp_file = "ms_print.tmp.$$";

# Version number.
my $version = "3.5.0-Debian";

# Args passed, for printing.
my $ms_print_args;

# Usage message.
my $usage = <<END
usage: ms_print [options] massif-out-file

  options for the user, with defaults in [ ], are:
    -h --help             show this message
    --version             show version
    --threshold=<m.n>     significance threshold, in percent [$threshold]

  ms_print is Copyright (C) 2007-2007 Nicholas Nethercote.
  and licensed under the GNU General Public License, version 2.
  Bug reports, feedback, admiration, abuse, etc, to: njn\@valgrind.org.
                                                
END
;

# Used in various places of output.
my $fancy    = '-' x 80;
my $fancy_nl = $fancy . "\n";

# Returns 0 if the denominator is 0.
sub safe_div_0($$)
{
    my ($x, $y) = @_;
    return ($y ? $x / $y : 0);
}

#-----------------------------------------------------------------------------
# Argument and option handling
#-----------------------------------------------------------------------------
sub process_cmd_line() 
{
    my @files;

    # Grab a copy of the arguments, for printing later.
    for my $arg (@ARGV) { 
        $ms_print_args .= " $arg";       # The arguments.
    }

    for my $arg (@ARGV) { 

        # Option handling
        if ($arg =~ /^-/) {

            # --version
            if ($arg =~ /^--version$/) {
                die("ms_print-$version\n");

            # --threshold=X (tolerates a trailing '%')
            } elsif ($arg =~ /^--threshold=([\d\.]+)%?$/) {
                $threshold = $1;
                ($1 >= 0 && $1 <= 100) or die($usage);

            } else {            # -h and --help fall under this case
                die($usage);
            }
        } else {
            # Not an option.  Remember it as a filename. 
            push(@files, $arg);
        }
    }

    # Must have chosen exactly one input file.
    if (scalar @files) {
        $input_file = $files[0];
    } else {
        die($usage);
    }
}

#-----------------------------------------------------------------------------
# Reading the input file: auxiliary functions
#-----------------------------------------------------------------------------

# Gets the next line, stripping comments and skipping blanks.
# Returns undef at EOF.
sub get_line()
{
    while (my $line = <INPUTFILE>) {
        $line =~ s/#.*$//;          # remove comments
        if ($line !~ /^\s*$/) {
            return $line;           # return $line if non-empty
        }
    }
    return undef;       # EOF: return undef
}

sub equals_num_line($$)
{
    my ($line, $fieldname) = @_;
    defined($line) 
        or die("Line $.: expected \"$fieldname\" line, got end of file\n");
    $line =~ s/^$fieldname=(.*)\s*$//
        or die("Line $.: expected \"$fieldname\" line, got:\n$line");
    return $1;
}

sub is_significant_XPt($$$)
{
    my ($is_top_node, $xpt_szB, $total_szB) = @_;
    ($xpt_szB <= $total_szB) or die;
    # Nb: we always consider the alloc-XPt significant, even if the size is
    # zero.
    return $is_top_node || 0 == $threshold ||
        ( $total_szB != 0 && $xpt_szB * 100 / $total_szB >= $threshold );
}

#-----------------------------------------------------------------------------
# Reading the input file: reading heap trees
#-----------------------------------------------------------------------------

# Forward declaration, because it's recursive.
sub read_heap_tree($$$$$);

# Return pair:  if the tree was significant, both are zero.  If it was
# insignificant, the first element is 1 and the second is the number of
# bytes.
sub read_heap_tree($$$$$)
{
    # Read the line and determine if it is significant.
    my ($is_top_node, $this_prefix, $child_midfix, $arrow, $mem_total_B) = @_;
    my $line = get_line();
    (defined $line and $line =~ /^\s*n(\d+):\s*(\d+)(.*)$/)
        or die("Line $.: expected a tree node line, got:\n$line\n");
    my $n_children = $1;
    my $bytes      = $2;
    my $details    = $3;
    my $perc       = safe_div_0(100 * $bytes, $mem_total_B);
    # Nb: we always print the alloc-XPt, even if its size is zero.
    my $is_significant = is_significant_XPt($is_top_node, $bytes, $mem_total_B);

    # We precede this node's line with "$this_prefix.$arrow".  We precede
    # any children of this node with "$this_prefix$child_midfix$arrow".
    if ($is_significant) {
        # Nb: $details might have '%' in it, so don't embed directly in the
        # format string.
        printf(TMPFILE
            "$this_prefix$arrow%05.2f%% (%sB)%s\n", $perc, commify($bytes),
            $details);
    }

    # Now read all the children.
    my $n_insig_children = 0;
    my $total_insig_children_szB = 0;
    my $this_prefix2 = $this_prefix . $child_midfix;
    for (my $i = 0; $i < $n_children; $i++) {
        # If child is the last sibling, the midfix is empty.
        my $child_midfix2 = ( $i+1 == $n_children ? "  " : "| " );
        my ($is_child_insignificant, $child_insig_bytes) =
            # '0' means it's not the top node of the tree.
            read_heap_tree(0, $this_prefix2, $child_midfix2, "->",
                $mem_total_B);
        $n_insig_children += $is_child_insignificant;
        $total_insig_children_szB += $child_insig_bytes;
    }

    if ($is_significant) {
        # If this was significant but any children were insignificant, print
        # the "in N places" line for them.
        if ($n_insig_children > 0) {
            $perc = safe_div_0(100 * $total_insig_children_szB, $mem_total_B);
            printf(TMPFILE "%s->%05.2f%% (%sB) in %d+ places, all below "
                 . "ms_print's threshold (%05.2f%%)\n",
                $this_prefix2, $perc, commify($total_insig_children_szB),
                $n_insig_children, $threshold);
            print(TMPFILE "$this_prefix2\n");
        }

        # If this node has no children, print an extra (mostly) empty line.
        if (0 == $n_children) {
            print(TMPFILE "$this_prefix2\n");
        }
        return (0, 0);

    } else {
        return (1, $bytes);
    }
}

#-----------------------------------------------------------------------------
# Reading the input file: main
#-----------------------------------------------------------------------------

sub max_label_2($$)
{
    my ($szB, $szB_scaled) = @_;

    # For the label, if $szB is 999B or below, we print it as an integer.
    # Otherwise, we print it as a float with 5 characters (including the '.').
    # Examples (for bytes):
    #       1 -->     1  B
    #     999 -->   999  B
    #    1000 --> 0.977 KB
    #    1024 --> 1.000 KB
    #   10240 --> 10.00 KB
    #  102400 --> 100.0 KB
    # 1024000 --> 0.977 MB
    # 1048576 --> 1.000 MB
    #
    if    ($szB < 1000)        { return sprintf("%5d",   $szB);        }
    elsif ($szB_scaled < 10)   { return sprintf("%5.3f", $szB_scaled); }
    elsif ($szB_scaled < 100)  { return sprintf("%5.2f", $szB_scaled); }
    else                       { return sprintf("%5.1f", $szB_scaled); }
}

# Work out the units for the max value, measured in instructions.
sub i_max_label($)
{
    my ($nI) = @_;

    # We repeat until the number is less than 1000.
    my $nI_scaled = $nI;
    my $unit = "i";
    # Nb: 'k' is the "kilo" (1000) prefix.
    if ($nI_scaled >= 1000) { $unit = "ki"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Mi"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Gi"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Ti"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Pi"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Ei"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Zi"; $nI_scaled /= 1024; }
    if ($nI_scaled >= 1000) { $unit = "Yi"; $nI_scaled /= 1024; }

    return (max_label_2($nI, $nI_scaled), $unit);
}

# Work out the units for the max value, measured in bytes.
sub B_max_label($)
{
    my ($szB) = @_;

    # We repeat until the number is less than 1000, but we divide by 1024 on
    # each scaling.
    my $szB_scaled = $szB;
    my $unit = "B";
    # Nb: 'K' or 'k' are acceptable as the "binary kilo" (1024) prefix.
    # (Strictly speaking, should use "KiB" (kibibyte), "MiB" (mebibyte), etc,
    # but they're not in common use.)
    if ($szB_scaled >= 1000) { $unit = "KB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "MB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "GB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "TB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "PB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "EB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "ZB"; $szB_scaled /= 1024; }
    if ($szB_scaled >= 1000) { $unit = "YB"; $szB_scaled /= 1024; }

    return (max_label_2($szB, $szB_scaled), $unit);
}

# Work out the units for the max value, measured in ms/s/h.
sub t_max_label($)
{
    my ($szB) = @_;

    # We scale from millisecond to seconds to hours.
    #
    # XXX: this allows a number with 6 chars, eg. "3599.0 s"
    my $szB_scaled = $szB;
    my $unit = "ms";
    if ($szB_scaled >= 1000) { $unit = "s"; $szB_scaled /= 1000; }
    if ($szB_scaled >= 3600) { $unit = "h"; $szB_scaled /= 3600; }

    return (max_label_2($szB, $szB_scaled), $unit);
}

# This prints four things:
#   - the output header
#   - the graph
#   - the snapshot summaries (number, list of detailed ones)
#   - the snapshots
#
# The first three parts can't be printed until we've read the whole input file;
# but the fourth part is much easier to print while we're reading the file.  So
# we print the fourth part to a tmp file, and then dump the tmp file at the
# end.
#
sub read_input_file() 
{
    my $desc = "";              # Concatenated description lines.
    my $peak_mem_total_szB = 0;

    # Info about each snapshot.
    my @snapshot_nums = ();
    my @times         = ();
    my @mem_total_Bs  = ();
    my @mem_heap_Bs = ();
    my @mem_heap_extra_Bs = ();
    my @mem_stacks_Bs = ();
    my @is_detaileds  = ();
    my $peak_num = -1;      # An initial value that will be ok if no peak
                            # entry is in the file.
    
    #-------------------------------------------------------------------------
    # Read start of input file.
    #-------------------------------------------------------------------------
    open(INPUTFILE, "< $input_file") 
         || die "Cannot open $input_file for reading\n";

    # Read "desc:" lines.
    my $line;
    while ($line = get_line()) {
        if ($line =~ s/^desc://) {
            $desc .= $line;
        } else {
            last;
        }
    }

    # Read "cmd:" line (Nb: will already be in $line from "desc:" loop above).
    ($line =~ /^cmd:\s*(.*)$/) or die("Line $.: missing 'cmd' line\n");
    $cmd = $1;

    # Read "time_unit:" line.
    $line = get_line();
    ($line =~ /^time_unit:\s*(.*)$/) or
        die("Line $.: missing 'time_unit' line\n");
    $time_unit = $1;

    #-------------------------------------------------------------------------
    # Print snapshot list header to $tmp_file.
    #-------------------------------------------------------------------------
    open(TMPFILE, "> $tmp_file") 
         || die "Cannot open $tmp_file for reading\n";

    my $time_column = sprintf("%14s", "time($time_unit)");
    my $column_format = "%3s %14s %16s %16s %13s %12s\n";
    my $header =
        $fancy_nl .
        sprintf($column_format
        ,   "n"
        ,   $time_column
        ,   "total(B)"
        ,   "useful-heap(B)"
        ,   "extra-heap(B)"
        ,   "stacks(B)"
        ) .
        $fancy_nl;
    print(TMPFILE $header);

    #-------------------------------------------------------------------------
    # Read body of input file.
    #-------------------------------------------------------------------------
    $line = get_line();
    while (defined $line) {
        my $snapshot_num     = equals_num_line($line,      "snapshot");
        my $time             = equals_num_line(get_line(), "time");
        my $mem_heap_B       = equals_num_line(get_line(), "mem_heap_B");
        my $mem_heap_extra_B = equals_num_line(get_line(), "mem_heap_extra_B");
        my $mem_stacks_B     = equals_num_line(get_line(), "mem_stacks_B");
        my $mem_total_B      = $mem_heap_B + $mem_heap_extra_B + $mem_stacks_B;
        my $heap_tree        = equals_num_line(get_line(), "heap_tree");

        # Print the snapshot data to $tmp_file.
        printf(TMPFILE $column_format,
        ,   $snapshot_num
        ,   commify($time)
        ,   commify($mem_total_B)
        ,   commify($mem_heap_B)
        ,   commify($mem_heap_extra_B)
        ,   commify($mem_stacks_B)
        );

        # Remember the snapshot data.
        push(@snapshot_nums, $snapshot_num);
        push(@times,         $time);
        push(@mem_heap_Bs,  $mem_heap_B);
        push(@mem_heap_extra_Bs,  $mem_heap_extra_B);
        push(@mem_stacks_Bs,  $mem_stacks_B);
        push(@mem_total_Bs,  $mem_total_B);
        push(@is_detaileds,  ( $heap_tree eq "empty" ? 0 : 1 ));
        $peak_mem_total_szB = $mem_total_B
            if $mem_total_B > $peak_mem_total_szB;

        # Read the heap tree, and if it's detailed, print it and a subsequent
        # snapshot list header to $tmp_file.
        if      ($heap_tree eq "empty") {
            $line = get_line();
        } elsif ($heap_tree =~ "(detailed|peak)") {
            # If "peak", remember the number.
            if ($heap_tree eq "peak") {
                $peak_num = $snapshot_num;
            }
            # '1' means it's the top node of the tree.
            read_heap_tree(1, "", "", "", $mem_total_B);

            # Print the header, unless there are no more snapshots.
            $line = get_line();
            if (defined $line) {
                print(TMPFILE $header);
            }
        } else {
            die("Line $.: expected 'empty' or '...' after 'heap_tree='\n");
        }
    }

    close(INPUTFILE);
    close(TMPFILE);

    #-------------------------------------------------------------------------
    # Print header.
    #-------------------------------------------------------------------------
    print($fancy_nl);
    print("Command:            $cmd\n");
    print("Massif arguments:  $desc");
    print("ms_print arguments:$ms_print_args\n");
    print($fancy_nl);
    print("\n\n");

    #-------------------------------------------------------------------------
    # Setup for graph.
    #-------------------------------------------------------------------------
    # The ASCII graph.
    # Row    0 is the X-axis.
    # Column 0 is the Y-axis.
    # The rest ([1][1]..[graph_x][graph_y]) is the usable graph area.
    my @graph;
    my $x;
    my $y;

    my $gd_graph_data = GD::Graph::Data->new()
      or die GD::Graph::Data->error;
   
    my $n_snapshots = scalar(@snapshot_nums);
    ($n_snapshots > 0) or die;
    my $end_time = $times[$n_snapshots-1];
    ($end_time >= 0) or die;

    #-------------------------------------------------------------------------
    # Write snapshot bars into graph[][].
    #-------------------------------------------------------------------------
    # Each row represents K bytes, which is 1/graph_y of the peak size
    # (and K can be non-integral).  When drawing the column for a snapshot,
    # in order to fill the slot in row y (where the first row drawn on is
    # row 1) with a full-char (eg. ':'), it must be >= y*K.  For example, if
    # K = 10 bytes, then the values 0, 4, 5, 9, 10, 14, 15, 19, 20, 24, 25,
    # 29, 30 would be drawn like this (showing one per column):
    #
    #                       y    y * K
    #                       -    -----------
    # 30 |            :     3    3 * 10 = 30
    # 20 |        :::::     2    2 * 10 = 20
    # 10 |    :::::::::     1    1 * 10 = 10
    # 0  +-------------

    my $normal_char   = ':';

    # Work out how many bytes each row represents.  If the peak size was 0,
    # make it 1 so that the Y-axis covers a non-zero range of values.
    # Likewise for end_time.
    if (0 == $peak_mem_total_szB) { $peak_mem_total_szB = 1; }
    if (0 == $end_time          ) { $end_time           = 1; }
    my $K = $peak_mem_total_szB;

       $x          = 0;

    #print "DEBUG: n_snapshots=$n_snapshots\n";

    for (my $i = 0; $i < $n_snapshots; $i++) {

        # Fill an array for one column for an x item in the GD::Data. 
        my @gd_row;
        $gd_row[0] = $times[$i];
 
        # Work out which column this snapshot belongs to.
        # TODO: Make the x axis proportional, not just a set of items.
        my $x_pos_frac = ($times[$i] / ($end_time));
        $x = int($x_pos_frac) + 1;    # +1 due to Y-axis

        #Y axis values:
        $gd_row[1] = $mem_heap_Bs[$i];
        $gd_row[2] = $mem_heap_extra_Bs[$i];
        $gd_row[3] = $mem_stacks_Bs[$i];

        $gd_graph_data->add_point(@gd_row);
    }

    #-------------------------------------------------------------------------
    # Print graph[][].
    #-------------------------------------------------------------------------

    # Make sure that all arrays are properly sized and initialized,
    # just to avoid crashes in unexpected situations.
    $gd_graph_data->make_strict();

    # Specify a large area so people can zoom in:
    my $gd_graph = GD::Graph::area->new(1024, 798);
    my @legend = ("Heap", "Extra Heap", "Stacks");
    $gd_graph->set_legend(@legend); 

    $gd_graph->set(
        #show_values => $gd_graph_data,
        x_label => 'Instructions (millions)',
        y_label => 'Kilobytes (KiB)',
        title   => 'Massif Snapshots',
        cumulate => 1, # Meaning True
        #long_ticks => 1, 
        tick_length => 0,
        #x_ticks => 0,
        #y_ticks => 0,
        #shadow_depth => 4,
        #shadowclr => 'dred',
        transparent => 0,
        'bgclr' => 'white', 
        #'dclrs' => [ qw(lblue lyellow blue yellow lgreen lred green red purple orange pink dyellow) ], 
        accent_treshold => 100_000, # Don't draw the vertical lines for each x item.

        # Try to have a margin around the whole drawing, though this does not seem to work:
        t_margin => 20,
        b_margin => 20,
        l_margin => 20,
        r_margin => 20
        )
        or warn $gd_graph->error;

    my $gd = $gd_graph->plot($gd_graph_data)
        or die $gd_graph->error;

    open(IMG, ">massif_pretty.png") or die $!;
    binmode IMG;
    print IMG $gd->png;
}

#-----------------------------------------------------------------------------
# Misc functions
#-----------------------------------------------------------------------------
sub commify ($) {
    my ($val) = @_;
    1 while ($val =~ s/^(\d+)(\d{3})/$1,$2/);
    return $val;
}


#----------------------------------------------------------------------------
# "main()"
#----------------------------------------------------------------------------
process_cmd_line();
read_input_file();

##--------------------------------------------------------------------##
##--- end                                              ms_print.in ---##
##--------------------------------------------------------------------##
