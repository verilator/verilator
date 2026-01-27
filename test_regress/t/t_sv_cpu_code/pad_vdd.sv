// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed under the Creative Commons Public Domain, for
// SPDX-FileCopyrightText: 2012
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

//*****************************************************************************
// PAD_VDD - VDD Supply Pad (Dummy!!!!)
//*****************************************************************************

module pad_vdd
#( parameter ID = 0 )
  (
   inout wire pad
   );

  assign pad = 1'b1;
endmodule // pad_vdd
