// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

// *****************************************************************************
// Code ROM
//
// IMPORTANT!
//   Array size must be uppdated according to program size.
// *****************************************************************************

const
  logic [15:0] rom[0:13]
  = '{
      `LDI( R0, 11 )
      `LDI( R1, 22 )
      `LDI( R2, 33 )
      `LDI( R3, 44 )

      `STS(  0, R0 )
      `STS(  1, R1 )
      `STS(  2, R2 )
      `STS(  3, R3 )

      `LDS(  R4, 0 )
      `LDS(  R5, 1 )
      `LDS(  R6, 0 )
      `LDS(  R7, 0 )

      `JMP( 00 )

      `EOP                      // End of Program (NOP)
      };
