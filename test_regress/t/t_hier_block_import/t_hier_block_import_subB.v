// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Note: no hier_block pragma here to validate partial hier_block design
module subB (output bit [31:0] out);
   assign out = `VALUE_B;
endmodule
