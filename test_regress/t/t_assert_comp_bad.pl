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

compile(
    verilator_flags2 => ['--assert'],
    nc_flags2 => ['+assert'],
    vcs_flags2 => ['-assert svaext'],
    fails => 1,
    expect_filename => $Self->{golden_filename},
    );

extract(
    in => $Self->{top_filename},
    out => "../docs/gen/ex_USERWARN_faulty.rst",
    regexp => qr/\$warn.*User/);

extract(
    in => $Self->{top_filename},
    out => "../docs/gen/ex_USERERROR_faulty.rst",
    regexp => qr/\$error.*User/);

extract(
    in => $Self->{top_filename},
    out => "../docs/gen/ex_USERINFO_faulty.rst",
    regexp => qr/\$info.*User/);

extract(
    in => $Self->{top_filename},
    out => "../docs/gen/ex_USERFATAL_faulty.rst",
    regexp => qr/\$fatal.*User/);

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_USERWARN_msg.rst",
    regexp => qr/USERWARN:.* User/);

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_USERERROR_msg.rst",
    regexp => qr/USERERROR:.* User/);

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_USERINFO_msg.rst",
    regexp => qr/-Info:.* User/);

extract(
    in => $Self->{golden_filename},
    out => "../docs/gen/ex_USERFATAL_msg.rst",
    regexp => qr/USERFATAL/);

ok(1);
1;
