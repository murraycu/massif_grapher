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

# This it the libchart-gnuplot-perl package on Ubuntu/Debian.

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
    --threshold=<m.n>     significance threshold, in percent [$threshold] (specify this to massif too).
    --detailed            Print allocation details, using only the detailed snapshots.

  massif_grapher is Copyright (C) 2007-2007 Nicholas Nethercote, and Copyright (C) 2009 Murray Cumming 
  and licensed under the GNU General Public License, version 2.
  Bug reports, feedback, admiration, abuse, etc, to: njn\@valgrind.org.


  For best results run valgrind massif with --details-freq=1. For instance,
    valgrind --tool=massif --detailed-freq=1 yourapp
                                                
END
;

# Used in various places of output.
my $fancy    = '-' x 80;
my $fancy_nl = $fancy . "\n";

# Details of the snapshots' trees:
# Arrays of references to arrays:
my @snapshot_nums = ();
my @times         = ();
my @mem_heap_parts = ();
my @mem_heap_part_names = ();
my @mem_heap_Bs = ();
my @mem_heap_extra_Bs = ();
my @mem_stacks_Bs = ();
my @is_detaileds  = ();
my $peak_mem_total_szB = 0;

# Map of all function names to a unique index:
my %hash_map_part_names = (); 
# Reverse (Map of all unique indexes to function names):
my %hash_map_part_names_reverse = ();
# Map of all function names to an array of the bytes (for each snapshot).
my %hash_map_part_bytes = (); 


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

    # Info about each snapshot.
    my @mem_total_Bs  = ();
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

        #TODO: Or change the formatting on the graph?
        $mem_heap_B = $mem_heap_B / 1024;
        $mem_heap_extra_B = $mem_heap_extra_B / 1024;
        $mem_stacks_B = $mem_stacks_B / 1024;
        $time = $time / 1000000;

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

              #Initialize the bytes array for this function name too:
              my @bytes = ();
              $hash_map_part_bytes{$function_name} = \@bytes;

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
}

# Returns the temp file name and the gnuplot using string to map that to the graph.
sub save_data_to_temp_file() {

    my $file = 'gnuplot.dat';
    open (TABLE, ">$file");

    #Print the column titles:
    print TABLE "Time";

    if ($arg_detailed) {
        foreach my $id (sort {$a <=> $b} keys (%hash_map_part_names_reverse)) {
            my $function_name = $hash_map_part_names_reverse{$id};
            print TABLE "\t" . $function_name;
        }
    } else {
        print TABLE "\tHeap\tExtra Heap\tStack";
    }

    print TABLE "\n";

    # Print the contents of the arrays:
    my $n_snapshots = scalar(@snapshot_nums);
    for (my $i = 0; $i < $n_snapshots; $i++) {

        if ($arg_detailed) {

            if ($is_detaileds[$i]) {
                print TABLE $times[$i];

                my $heap_parts_ref = $mem_heap_parts[$i];
                my @heap_parts_bytes = @$heap_parts_ref;
            
                foreach my $id (sort {$a <=> $b} keys (%hash_map_part_names_reverse)) {
                     my $function_name = $hash_map_part_names_reverse{$id};
                     my $bytes_ref = $hash_map_part_bytes{$function_name};
                     my @bytes = @$bytes_ref;

                     print TABLE "\t" . @bytes[$i];
                }
            }
        } else {
            print TABLE $times[$i];
            print TABLE "\t" . $mem_heap_Bs[$i];
            print TABLE "\t" . $mem_heap_extra_Bs[$i];
            print TABLE "\t" . $mem_stacks_Bs[$i];
        }

        print TABLE "\n";

    }
    close (TABLE);

    my $using = "";

    # Construct the "using" string for the DataSet object.
    # This tells gnuplot what to do with each column from the data file.
    # Note that the columns are 1-indexed, not 0-indexed.
    if ($arg_detailed) {
        $using = "";

        my $col_index = 1;
        foreach my $id (sort {$a <=> $b} keys (%hash_map_part_names_reverse)) {
          my $title = $hash_map_part_names_reverse{$id};

          if($using eq "") {
            $using = "2:xtic(1)";
          } else {
            # '' seems to mean "the same data file as previously mentioned". 
            $using .= ", '' using " . $col_index;
          }

          $col_index++;
        }
    } else {
        $using = "2:xtic(1)";
        # '' seems to mean "the same data file as previously mentioned". 
        $using .= ", '' using 3";
        $using .= ", '' using 4";
    }

    print "debug: using=" . $using . "\n";

    return ($file, $using);
}

sub print_graph() {

    #-------------------------------------------------------------------------
    # Setup for graph.
    #-------------------------------------------------------------------------

    my @data_sets = ();
    my $data_set = undef;

    # Work out how many bytes each row represents.  If the peak size was 0,
    # make it 1 so that the Y-axis covers a non-zero range of values.
    if (0 == $peak_mem_total_szB) { $peak_mem_total_szB = 1; }
    my $K = $peak_mem_total_szB;


    if ($arg_detailed) {

        my $n_snapshots = scalar(@snapshot_nums);
        ($n_snapshots > 0) or die;

        my @times_detailed = (); 

        # Make sure that all bytes arrays are big enough, and zeroed,
        # for each function name, even if they are not mentioned in every snapshot:
        my $n_snapshots_detailed = 0;
        for (my $i = 0; $i < $n_snapshots; $i++) {
            if ($is_detaileds[$i]) {
                $n_snapshots_detailed++;
            }
        }

        my $n_functions = scalar( keys (%hash_map_part_bytes) );
        foreach my $function_name (keys (%hash_map_part_bytes)) {
            my $bytes_ref = $hash_map_part_bytes{$function_name};
            my @bytes = @$bytes_ref;

            for(my $i = 0; $i < $n_snapshots_detailed; $i++) {
                $bytes[$i] = 0;
            }

            #print "debug: function_name=" . $function_name  . "\n";
            #print "  debug: zeroed size=" . scalar(@bytes) . "\n";

            #TODO: How can we make this unnnecessary?
            #Without doing this we seem to be just changing a copy of the array.
            $hash_map_part_bytes{$function_name} = \@bytes;

            #my $bytes_ref2 = $hash_map_part_bytes{$function_name};
            #my @bytes2 = @$bytes_ref2;
            #print "  debug: zeroed size2=" . scalar(@bytes2) . "\n";
        }

        # Look at each snapshot, and get the bytes for each function:
        my $i_detailed = 0;
        for (my $i = 0; $i < $n_snapshots; $i++) {

            #Y axis values:
            if ($is_detaileds[$i]) {
                # Detailed values, with a y value for each function that is 
                # mentioned in any snapshot:

                $times_detailed[$i_detailed] = $times[$i];

                my $heap_parts_ref = $mem_heap_parts[$i];
                my @heap_parts_bytes = @$heap_parts_ref;

                my $heap_parts_names_ref = $mem_heap_part_names[$i];
                my @heap_parts_names = @$heap_parts_names_ref;

                my $index = 0;
                foreach my $function_name (@heap_parts_names) {
                    my $bytes = $heap_parts_bytes[$index];
                   
                    my $id = $hash_map_part_names{$function_name};
                    my $dataset_array_ref = $hash_map_part_bytes{$function_name};
                    my @dataset_array = @$dataset_array_ref;
                    $dataset_array[$i_detailed] = $bytes / 1024; #TODO: Or change the formatting on the graph?

                    #TODO: How can we make this unnnecessary?
                    #Without doing this we seem to be just changing a copy of the array.
                    $hash_map_part_bytes{$function_name} = \@dataset_array;

                    $index++;
                }

                $i_detailed++;
            }
        }
    }

    #-------------------------------------------------------------------------
    # Print graph[][].
    #-------------------------------------------------------------------------

    # We save the data to a temporary file and tell Chart::Gnuplot to use 
    # that file, because that is the only way to use the histograms rowstacked 
    # style with the Chart::Gnuplot perl API, according to its (helpful) 
    # maintainer, Ka-Wai Mak:  
    my ($filename_temp, $gnuplot_using) = save_data_to_temp_file();


    open (GNUPLOT, "| gnuplot");
    print GNUPLOT <<EOPLOT;
set terminal postscript enhanced color size 80cm,29.7cm
set output 'massif_pretty.ps'
set datafile separator '\t'
set key autotitle columnheader
set style data histogram
set style histogram rowstacked
set style fill solid border -1
set xlabel 'Instructions (millions)'
set ylabel 'Kilobytes (KiB)'
set key outside bottom reverse
set xtics nomirror rotate by 90
set format x "%.0f"
set ytics nomirror
set format y "%.0fk"
plot '$filename_temp' using $gnuplot_using
EOPLOT
    close (GNUPLOT);
}

#----------------------------------------------------------------------------
# "main()"
#----------------------------------------------------------------------------
process_cmd_line();
read_input_file();
print_graph();

##--------------------------------------------------------------------##
##--- end                                              ms_print.in ---##
##--------------------------------------------------------------------##
