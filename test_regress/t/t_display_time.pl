#!/usr/bin/perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003 by Wilson Snyder. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

$Self->{vl_time_multiplier} = 1000;

compile (
    verilator_flags2 => ['-DVL_TIME_MULTIPLER=1000'],
    );

execute (
	 check_finished=>1,
	 expect=> quotemeta(
'default:   [0.000] 0t time [               0.000] No0 time
'
# Unsupported:
#'default:   [0] 0t time [                   0] No0 time
#-9,0,,0:   [0] 0t time [0] No0 time
#-9,0,,10:  [0] 0t time [         0] No0 time
#-9,0,ns,5: [0ns] 0t time [  0ns] No0 time
#-9,3,ns,8: [0.000ns] 0t time [ 0.000ns] No0 time
#'
),
     );

ok(1);
1;
