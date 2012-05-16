// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

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
