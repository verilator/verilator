// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (input logic[31:0] in, output logic[31:0] out);
   assign out = in;
endmodule
