#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

use IO::File;
use POSIX qw(strftime);
use strict;
use File::Spec::Functions 'catfile';

scenarios(dist => 1);

our $Release_Ok_Re = qr!(^test_regress/t/|^examples/)!;
our $Exempt_Author_Re = qr!(^ci/|^nodist/fastcov.py|^nodist/fuzzer|^test_regress/t/.*\.(v|cpp|h)$)!;
our $Exempt_Files_Re = qr!(^\.|/\.|\.gitignore$|\.dat|\.gprof|\.mem|\.out$|\.png$|\.tree|\.vc$|\.vcd$|^\.)!;
our @Exempt_Files_List = qw(
    Artistic
    CPPLINT.cfg
    LICENSE
    README.rst
    ci/ci-win-compile.ps1
    ci/ci-win-test.ps1
    ci/coverage-upload.sh
    docs/CONTRIBUTING.rst
    docs/CONTRIBUTORS
    docs/README.rst
    docs/_static
    docs/gen
    docs/spelling.txt
    docs/verilated.dox
    include/gtkwave
    include/vltstd
    install-sh
    src/mkinstalldirs
    test_regress/t/t_altera_lpm.v
    test_regress/t/t_flag_f__3.v
    test_regress/t/t_fuzz_eof_bad.v
    test_regress/t/t_incr_void.v
    test_regress/t/t_timing_trace_fst.pl
    test_regress/t/t_uvm_pkg_all.vh
    test_regress/t/t_uvm_pkg_todo.vh
    test_regress/t/t_wrapper_context.pl
    test_regress/t/t_wrapper_context_fst.pl
    test_regress/t/t_wrapper_context_seq.pl
    test_regress/t/t_wrapper_del_context_bad.pl
    test_regress/t/tsub/t_flag_f_tsub.v
    test_regress/t/tsub/t_flag_f_tsub_inc.v
    verilator.pc.in
    );

our @Exempt_Files_Copyright = qw(
    test_regress/t/t_assert_disable_bad.pl
    test_regress/t/t_clocking_bad1.pl
    test_regress/t/t_clocking_bad2.pl
    test_regress/t/t_clocking_bad3.pl
    test_regress/t/t_clocking_bad4.pl
    test_regress/t/t_clocking_notiming.pl
    test_regress/t/t_clocking_timing2.pl
    test_regress/t/t_clocking_unsup1.pl
    test_regress/t/t_clocking_unsup2.pl
    test_regress/t/t_comb_input_0.pl
    test_regress/t/t_comb_input_1.pl
    test_regress/t/t_comb_input_2.pl
    test_regress/t/t_comb_loop_through_unpacked_array.pl
    test_regress/t/t_const_bitoptree_bug3096.pl
    test_regress/t/t_const_sel_sel_extend.pl
    test_regress/t/t_delay_incr_timing.pl
    test_regress/t/t_delay_timing.pl
    test_regress/t/t_dfg_3676.pl
    test_regress/t/t_dfg_3726.pl
    test_regress/t/t_dfg_circular.pl
    test_regress/t/t_dfg_multidriver_dfg_bad.pl
    test_regress/t/t_dfg_multidriver_non_dfg.pl
    test_regress/t/t_dfg_peephole.pl
    test_regress/t/t_dfg_unhandled.pl
    test_regress/t/t_dist_cppstyle.pl
    test_regress/t/t_dpi_arg_inout_type.pl
    test_regress/t/t_dpi_arg_inout_unpack.pl
    test_regress/t/t_dpi_arg_input_type.pl
    test_regress/t/t_dpi_arg_input_unpack.pl
    test_regress/t/t_dpi_arg_output_type.pl
    test_regress/t/t_dpi_arg_output_unpack.pl
    test_regress/t/t_dpi_import_hdr_only.pl
    test_regress/t/t_dpi_open_query.pl
    test_regress/t/t_dpi_result_type.pl
    test_regress/t/t_dpi_result_type_bad.pl
    test_regress/t/t_dump_dfg.pl
    test_regress/t/t_event_control_expr.pl
    test_regress/t/t_event_control_expr_unsup.pl
    test_regress/t/t_event_control_timing.pl
    test_regress/t/t_flag_build_jobs_and_j.pl
    test_regress/t/t_flag_prefix.pl
    test_regress/t/t_flag_quiet_exit.pl
    test_regress/t/t_flag_structs_packed.pl
    test_regress/t/t_flag_values_deprecated.pl
    test_regress/t/t_fork_timing.pl
    test_regress/t/t_format_wide_decimal.pl
    test_regress/t/t_gate_basic_timing.pl
    test_regress/t/t_gate_delay_unsup.pl
    test_regress/t/t_gate_loop.pl
    test_regress/t/t_lib.pl
    test_regress/t/t_lib_nolib.pl
    test_regress/t/t_lib_prot.pl
    test_regress/t/t_lib_prot_clk_gated.pl
    test_regress/t/t_lib_prot_comb.pl
    test_regress/t/t_lib_prot_delay_bad.pl
    test_regress/t/t_lib_prot_inout_bad.pl
    test_regress/t/t_lib_prot_secret.pl
    test_regress/t/t_lib_prot_shared.pl
    test_regress/t/t_lint_wait_bad.pl
    test_regress/t/t_merge_cond_blowup.pl
    test_regress/t/t_merge_cond_bug_3409.pl
    test_regress/t/t_merge_cond_no_extend.pl
    test_regress/t/t_merge_cond_no_motion.pl
    test_regress/t/t_net_delay.pl
    test_regress/t/t_net_delay_timing_sc.pl
    test_regress/t/t_notiming.pl
    test_regress/t/t_notiming_off.pl
    test_regress/t/t_order_timing.pl
    test_regress/t/t_param_real2_collision.pl
    test_regress/t/t_recursive_module_bug.pl
    test_regress/t/t_recursive_module_bug_2.pl
    test_regress/t/t_sampled_expr_unsup.pl
    test_regress/t/t_scheduling_5.pl
    test_regress/t/t_scope_map.pl
    test_regress/t/t_std_identifier_bad.pl
    test_regress/t/t_timing_clkgen_unsup.pl
    test_regress/t/t_timing_cmake.pl
    test_regress/t/t_timing_debug1.pl
    test_regress/t/t_timing_debug2.pl
    test_regress/t/t_timing_dpi_unsup.pl
    test_regress/t/t_timing_fork_comb.pl
    test_regress/t/t_timing_func_bad.pl
    test_regress/t/t_timing_intra_assign.pl
    test_regress/t/t_timing_localevent_unsup.pl
    test_regress/t/t_timing_protect.pl
    test_regress/t/t_timing_unset1.pl
    test_regress/t/t_timing_unset2.pl
    test_regress/t/t_timing_unset3.pl
    test_regress/t/t_timing_zerodly_unsup.pl
    test_regress/t/t_trace_abort.pl
    test_regress/t/t_trace_abort_fst.pl
    test_regress/t/t_trace_abort_fst_sc.pl
    test_regress/t/t_trace_ascendingrange.pl
    test_regress/t/t_trace_ascendingrange_fst.pl
    test_regress/t/t_trace_ascendingrange_fst_sc.pl
    test_regress/t/t_trace_param_override.pl
    test_regress/t/t_trace_timing1.pl
    test_regress/t/t_type_param_collision.pl
    test_regress/t/t_wait_timing.pl
    test_regress/t/t_while_timing_control.pl
    test_regress/t/t_x_assign_0.pl
    test_regress/t/t_x_assign_1.pl
    test_regress/t/t_x_assign_unique_0.pl
    test_regress/t/t_x_assign_unique_1.pl
    );

my $root = "..";
my $Debug;

my $Exempt_Files_List_Re = '^(' . join('|', (map { quotemeta $_ } @Exempt_Files_List)) . ")";

if (!-r "$root/.git") {
    skip("Not in a git repository");
} else {
    my $out = `cd $root && git ls-files --exclude-standard`;
    my $year = strftime("%Y", localtime);
    my %files;
    $out =~ s/\s+/ /g;
    foreach my $filename (split /\s+/, $out) {
        next if $filename =~ /$Exempt_Files_Re/;
        next if $filename =~ /$Exempt_Files_List_Re/;
        $files{$filename} = 1;
    }

    # Exempt files added before Jun 1 2023, when we added this check
    # List hardcoded now, but obtained from:
    # $out = `cd $root && git ls-tree -r  \`git rev-list -1 --before="Jun 1 2023" HEAD\` --name-only`;
    my %oldFile;
    foreach my $file (@Exempt_Files_Copyright) { $oldFile{$file} = 1; }

    foreach my $file (sort keys %files) {
        my $filename = catfile($root, $file);
        next if !-r $filename;
        my $fh = IO::File->new("<$filename") or error("$! $filename");
        next if !$fh;
        my $spdx;
        my $copyright;
        my $release;
        while (my $line = $fh->getline) {
            if ($line =~ /SPDX-License-Identifier:/) {
                $spdx = $line;
            } elsif ($line =~ /Copyright 20[0-9][0-9]/) {
                $copyright = $line;
                if ($line =~ /Wilson Snyder/) {
                } elsif ($oldFile{$file} && $line =~ /Antmicro|Geza Lore|Todd Strader/) {
                } elsif ($file =~ /$Exempt_Author_Re/) {
                } else {
                    my $yeardash = ($file =~ m!test_regress/t!) ? $year : $year."-".$year;
                    warn "   ".$copyright;
                    error("$file: Please use standard 'Copyright $yeardash by Wilson Snyder'");
                }
            } elsif ($line =~ m!Creative Commons Public Domain!
                     || $line =~ m!freely copied and/or distributed!
                     || $line =~ m!placed into the Public Domain!) {
                $release = 1;
            }
        }
        my $release_note;
        if ($release && $file !~ /$Release_Ok_Re/) {
            $release_note = " (has copyright release, but not part of $Release_Ok_Re)";
        }
        if (!$copyright && (!$release || $release_note)) {
            error("$file: Please add standard 'Copyright $year ...', similar to in other files" . $release_note);
        }
        if (!$spdx) {
            error("$file: Please add standard 'SPDX-License_Identifier: ...', similar to in other files");
        }
    }
}

ok(1);
1;
