// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

//*****************************************************************************
// PAD_GND - Ground Supply Pad (Dummy!!!!)
//*****************************************************************************

module pad_gnd
#( parameter ID = 0 )
  (
   inout wire pad
   );

  assign pad = 1'b0;
endmodule // pad_gnd
