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

# This it the libgd-graph-perl package on Ubuntu/Debian.
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

# Whether the graph will be detailed, which requires us to only use 
# the details snapshots.
my $arg_detailed = 0;

# Input file name
my $input_file = undef;

# Version number.
my $version = "3.5.0-Debian";

# Args passed, for printing.
my $ms_print_args;

# Usage message.
my $usage = <<END
usage: massif_grapher [options] massif-out-file

  options for the user, with defaults in [ ], are:
    -h --help             show this message
    --version             show version
    --threshold=<m.n>     significance threshold, in percent [$threshold]
    --detailed            Print allocation details, using only the detailed snapshots.

  massif_grapher is Copyright (C) 2007-2007 Nicholas Nethercote, and Copyright (C) 2009 Murray Cumming 
  and licensed under the GNU General Public License, version 2.
  Bug reports, feedback, admiration, abuse, etc, to: njn\@valgrind.org.
                                                
END
;

# Used in various places of output.
my $fancy    = '-' x 80;
my $fancy_nl = $fancy . "\n";

# Details of the snapshots' trees:
# Arrays of references to arrays:
my @mem_heap_parts = ();
my @mem_heap_part_names = ();

# Map of all function names to a unique index:
my %hash_map_part_names = (); 
# Reverse (Map of all unique indexes to function names):
my %hash_map_part_names_reverse = ();

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

            } elsif ($arg =~ /^--detailed$/) {
                $arg_detailed = 1;

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

# Return four:
# The first element is the number of bytes,
# The second element is the name of the function.
# The second element is th array of child bytes.
# The third element is the array of child function names.
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

    # Now read all the children.
    my @child_bytes = ();
    my @child_functions = ();

    my $this_prefix2 = $this_prefix . $child_midfix;

    for (my $i = 0; $i < $n_children; $i++) {
        # If child is the last sibling, the midfix is empty.
        my $child_midfix2 = ( $i+1 == $n_children ? "  " : "| " );
        my ($this_size, $this_name, $ignored1, $ignored2) =
            read_heap_tree(0, $this_prefix2, $child_midfix2, "->",
                $mem_total_B);

        $child_bytes[$i] = $this_size;
        $child_functions[$i] = $this_name;
    }

    # Notice that we return array references, by using \@ instead of @.
    # Otherwise the contents of the second array would be put into the first array.
    return ($bytes, $details, \@child_bytes, \@child_functions)
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


    my $function_name_id = 1; #Start with 0 because row 0 is the Gd::Graph axis label

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

        my @child_bytes = ();
        my @child_functions = ();

        # Read the heap tree:
        if      ($heap_tree eq "empty") {
            $line = get_line();
        } elsif ($heap_tree =~ "(detailed|peak)") {
            # If "peak", remember the number.
            if ($heap_tree eq "peak") {
                $peak_num = $snapshot_num;
            }

            my ($bytes, $function_name, $child_bytes_ref, $child_functions_ref) = 
                read_heap_tree(1, "", "", "", $mem_total_B);
            @child_bytes = @$child_bytes_ref;
            @child_functions = @$child_functions_ref;

            $line = get_line();

        } else {
            die("Line $.: expected 'empty' or '...' after 'heap_tree='\n");
        }

        # Note that we add a reference (\@, not @) to the array,
        # instead of adding the array itself, to simplify things.
        push(@mem_heap_parts, \@child_bytes);
        push(@mem_heap_part_names, \@child_functions);

        # Process all discovered child functions, and assign a unqiue ID if necessary.
        # We use this to specify a heap size (y) for all functions at all times (x) in the cummulative graph.
        foreach (@child_functions) {
            my $function_name = $_;
            if (!(exists $hash_map_part_names{$function_name})) {
              $hash_map_part_names{$function_name} = $function_name_id;
              $hash_map_part_names_reverse{$function_name_id} = $function_name;
              $function_name_id++;
            }
        }

    }

    close(INPUTFILE);

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

    for (my $i = 0; $i < $n_snapshots; $i++) {

        # Fill an array for one column for an x item in the GD::Data. 
        my @gd_row;

        # The y item label (to appear for the item on the X axis):
        $gd_row[0] = $times[$i];
 
        # Work out which column this snapshot belongs to.
        # TODO: Make the x axis proportional, not just a set of items.
        my $x_pos_frac = ($times[$i] / ($end_time));
        $x = int($x_pos_frac) + 1;    # +1 due to Y-axis

        #Y axis values:
        if ($arg_detailed && $is_detaileds[$i]) {
            # Detailed values, with a y value for each function that is 
            # mentioned in any snapshot:

            # Default to 0 for all items,
            # to avoid undefined values.
            foreach my $id (keys(%hash_map_part_names_reverse)) {
                $gd_row[$id] = 0;
            }

            my $heap_parts_ref = $mem_heap_parts[$i];
            my @heap_parts_bytes = @$heap_parts_ref;

            my $heap_parts_names_ref = $mem_heap_part_names[$i];
            my @heap_parts_names = @$heap_parts_names_ref;

            my $index = 0;
            foreach my $function_name (@heap_parts_names) {
                my $bytes = $heap_parts_bytes[$index];
               
                my $id = $hash_map_part_names{$function_name};
                $gd_row[$id] = $bytes;

                $index++;
            }
        }
        else {
            # Just show the overall heap and stack values:
            $gd_row[1] = $mem_heap_Bs[$i];
            $gd_row[2] = $mem_heap_extra_Bs[$i];
            $gd_row[3] = $mem_stacks_Bs[$i];
        }

        $gd_graph_data->add_point(@gd_row);
    }

    #-------------------------------------------------------------------------
    # Print graph[][].
    #-------------------------------------------------------------------------

    # Make sure that all arrays are properly sized and initialized,
    # just to avoid crashes in unexpected situations.
    $gd_graph_data->make_strict();

    # Specify a large area so people can zoom in:
    # If this isn't big enough then we get a "Vertical size too small" error 
    # from Gd::Graph's axestype.pm: setup_boundaries().
    # Using the defaults (not specify a size) don't help either.
    # TODO: File a bug about that and/or guess a suitable size. 
    my $gd_graph = GD::Graph::area->new(2000, 2000);

    my @legend = ();

    if ($arg_detailed) {
        foreach my $id (keys(%hash_map_part_names_reverse)) {
            my $function_name = $hash_map_part_names_reverse{$id};
            push (@legend, $function_name)
        }
    }
    else {
        @legend = ("Heap", "Extra Heap", "Stacks");
    }

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

        t_margin => 20,
        b_margin => 20,
        l_margin => 20,
        r_margin => 20,

        y_min_value => 0,
        y_max_value => $peak_mem_total_szB,

        x_labels_vertical => 1
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
