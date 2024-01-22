#!/usr/bin/env perl
if (!$::Driver) { use FindBin; exec("$FindBin::Bin/bootstrap.pl", @ARGV, $0); die; }
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2003-2009 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

scenarios(simulator => 1);

my $out_filename = "$Self->{obj_dir}/V$Self->{name}.tree.json";

compile(
    verilator_flags2 => ["+define+ATTRIBUTES --no-json-edit-nums"],
    );

if ($Self->{vlt_all}) {
    file_grep("$out_filename", qr/{"type":"VAR","name":"clk0","addr":"[^"]*","loc":"e,74:[^"]*","origName":"clk0","isSc":false,"isPrimaryIO":true,"direction":"INPUT","isConst":false,"isPullup":false,"isPulldown":false,"isUsedClock":true,"isSigPublic":true,"isLatched":false,"isUsedLoopIdx":false,"noReset":false,"attrIsolateAssign":false,"attrFileDescr":false,"isDpiOpenArray":false,"isFuncReturn":false,"isFuncLocal":false,"attrClocker":"clker","lifetime":"NONE","varType":"PORT","sensIfacep":"UNLINKED","childDTypep": \[\],"delayp": \[\],"valuep": \[\],"attrsp": \[\]/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"clk1","addr":"[^"]*","loc":"e,75:[^"]*","origName":"clk1","isSc":false,"isPrimaryIO":true,"direction":"INPUT","isConst":false,"isPullup":false,"isPulldown":false,"isUsedClock":true,"isSigPublic":true,"isLatched":false,"isUsedLoopIdx":false,"noReset":false,"attrIsolateAssign":false,"attrFileDescr":false,"isDpiOpenArray":false,"isFuncReturn":false,"isFuncLocal":false,"attrClocker":"clker","lifetime":"NONE","varType":"PORT","sensIfacep":"UNLINKED","childDTypep": \[\],"delayp": \[\],"valuep": \[\],"attrsp": \[\]/);
    file_grep("$out_filename", qr/{"type":"VAR","name":"clk2","addr":"[^"]*","loc":"e,76:[^"]*","origName":"clk2","isSc":false,"isPrimaryIO":true,"direction":"INPUT","isConst":false,"isPullup":false,"isPulldown":false,"isUsedClock":false,"isSigPublic":true,"isLatched":false,"isUsedLoopIdx":false,"noReset":false,"attrIsolateAssign":false,"attrFileDescr":false,"isDpiOpenArray":false,"isFuncReturn":false,"isFuncLocal":false,"attrClocker":"clker","lifetime":"NONE","varType":"PORT","sensIfacep":"UNLINKED","childDTypep": \[\],"delayp": \[\],"valuep": \[\],"attrsp": \[\]/);
}

execute(
    check_finished => 1,
    );

ok(1);
1;
