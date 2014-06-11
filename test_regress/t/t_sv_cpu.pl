#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

# 22-Mar-2012: Modifications for this test contributed by Jeremy Bennett,
# Embecosm.

compile (
    # Taken from the original VCS command line.
    v_flags2 => ["t/t_sv_cpu_code/timescale.sv",
		 "t/t_sv_cpu_code/program_h.sv",
		 "t/t_sv_cpu_code/pads_h.sv",
		 "t/t_sv_cpu_code/ports_h.sv",
		 "t/t_sv_cpu_code/pinout_h.sv",
		 "t/t_sv_cpu_code/genbus_if.sv",
		 "t/t_sv_cpu_code/pads_if.sv",
		 "t/t_sv_cpu_code/adrdec.sv",
		 "t/t_sv_cpu_code/pad_gpio.sv",
		 "t/t_sv_cpu_code/pad_vdd.sv",
		 "t/t_sv_cpu_code/pad_gnd.sv",
		 "t/t_sv_cpu_code/pads.sv",
		 "t/t_sv_cpu_code/ports.sv",
		 "t/t_sv_cpu_code/ac_dig.sv",
		 "t/t_sv_cpu_code/ac_ana.sv",
		 "t/t_sv_cpu_code/ac.sv",
		 "t/t_sv_cpu_code/cpu.sv",
		 "t/t_sv_cpu_code/chip.sv"],
    vcs_flags2 => ["-R -sverilog +memcbk -y t/t_sv_cpu_code +libext+.sv+ +incdir+t/t_sv_cpu_code"],
    verilator_flags2 => ["-y t/t_sv_cpu_code +libext+.sv+ +incdir+t/t_sv_cpu_code --top-module t"],
    iv_flags2 => ["-yt/t_sv_cpu_code -It/t_sv_cpu_code -Y.sv"],
    );

execute (
    check_finished=>1,
     );

ok(1);
1;
