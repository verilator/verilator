// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

   export "DPI-C" function dpix_f_bit48;
   function bit [47:0] dpix_f_bit48(bit [47:0] i); dpix_f_bit48 = ~i; endfunction

endmodule
