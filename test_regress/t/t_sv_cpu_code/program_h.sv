// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

`ifndef _PROGRAM_H_V_
 `define _PROGRAM_H_V_

// *****************************************************************************
// Assembly Mnemonic Defines
// *****************************************************************************

typedef enum reg [3:0] { R0,R1,R2,R3,R4,R5,R6,R7,
                         R8,R9,R10,R11,R12,R13,R14,R15 } cpu_registers;

`define NOP            16'h0000,
`define JMP( k8 )      {4'h1, 4'h0, 8'h k8},
`define LDI( rd, k8 )  {4'h4,   rd, 8'h k8},
`define STS( k8, rs )  {4'h8,   rs, 8'h k8},
`define LDS( rd, k8 )  {4'h9,   rd, 8'h k8},
`define EOP            16'h0000



// *****************************************************************************
// Include ROM
// *****************************************************************************

`include "rom.sv"

`endif // !`ifdef _PROGRAM_H_V_
