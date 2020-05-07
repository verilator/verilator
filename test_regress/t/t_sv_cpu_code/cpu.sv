// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

module cpu
 #( parameter
      // ...
      ID   = 1 )                // Not used!
 (
  // ***************************************************************************
  // Module Interface (interfaces, outputs, and inputs)
  // ***************************************************************************

  // **** Interfaces ****
  genbus_if.master   dbus,


  // **** Outputs ****
  // N/A


  // **** Inputs ****
  input logic       clk,
  input logic       rst
 );

  // ***************************************************************************
  // Regs and Wires
  // ***************************************************************************

  // **** Program Memory ****
  logic [15:0] rom_out;


  // **** Register File (RF) ****
  logic [7:0]  rf[0:15];


  // **** Fetch Stage ****
  logic [7:0]  pc;              // PC -> Program counter.
  logic [15:0] ir;              // IR -> Instruction Register.


  // **** Decode ****
  logic [3:0]      idec_rd;
  logic            idec_rd_we;
  logic [7:0]      idec_rd_data;
  logic [3:0]      idec_rs;

  logic [7:0]      idec_nextpc; // New PC if change of program flow.

  logic            idec_coff;   // Indicates a change of program flow.

  logic [7:0]      idec_mem_adr;
  logic            idec_mem_re;
  logic            idec_mem_we;


  // **** Memory ****
  logic [7:0]      mem_data;    // Data from peripheral.
  logic            mem_ws;      // Waitstate.


  // ***************************************************************************
  // Program Memory (ROM) Interface
  // ***************************************************************************

  always_comb
    begin: ROM
      // - Local Variables -
      integer i;
      reg [15:0] irom [0:255];

      // - Set default -
      for ( i = 0; i < 256; i++ )
        begin
          if ( i < $size(rom) )
            irom[i] = rom[i];
          else
            irom[i] = 16'h0000;
        end

      rom_out = irom[pc[7:0]];
    end



  // ***************************************************************************
  // Register File (RF)
  // ***************************************************************************

  always_ff @( posedge clk )
    begin: RegFile
      // - Local Variables -
      integer i;

      // - Register File -
      for ( i = 0; i < 16; i++ )
        begin
          if ( rst )
            rf[i][7:0] <= 8'h00;
          else if ( idec_rd_we & (idec_rd == i[3:0]) )
            rf[i] <= idec_rd_data;
        end
    end



  // ***************************************************************************
  // Fetch Stage
  // ***************************************************************************

  // **** Program Counter (PC) / Instruction Register (IR) ****
  always_ff @( posedge clk )
    begin
      if ( rst )
        begin
          pc <= 8'h00;
          ir <= 16'h0000;
        end
      else //if ( ~mem_ws )
        begin
          if ( ~idec_coff )
            begin
              pc <= pc + 1;
              ir <= rom_out;    // Fetch Instruction.
            end
          else
            begin
              pc <= idec_nextpc;
              ir <= 16'h0000;   // Insert no operation (NOP).
            end
        end
    end



  // ***************************************************************************
  // Decode/Execute Stage
  // ***************************************************************************

  always_comb
    begin
      // - Defaults -
      idec_rd      = 4'h0;
      idec_rd_we   = 1'b0;
      idec_rd_data = 8'h00;
      idec_rs      = 4'h0;

      idec_nextpc  = 8'h00;
      idec_coff    = 1'b0;

      idec_mem_adr = 8'h00;
      idec_mem_re  = 1'b0;
      idec_mem_we  = 1'b0;

      // verilator lint_off CASEINCOMPLETE
      casez ( ir )
        16'h0000:;              // NOP (<=> Default)

        16'h1???:               // JMP imm
          begin
            idec_nextpc = ir[7:0];
            idec_coff   = 1'b1;
          end

        16'h4???:               // LDI rd, imm
          begin
            idec_rd      = ir[8+:4];
            idec_rd_we   = 1'b1;
            idec_rd_data = ir[0+:8];
          end

        16'h8???:
          begin                 // STS imm, rs
            idec_mem_adr = ir[0+:8];
            idec_mem_we  = 1'b1;
            idec_rs      = ir[8+:4];
          end

        16'h9???:
          begin                 // LDS rd, imm
            idec_mem_adr = ir[0+:8];
            idec_mem_we  = 1'b1;
            idec_rd      = ir[8+:4];
            idec_rd_we   = 1'b1;
            idec_rd_data = mem_data[0+:8];
          end
      endcase
    end



  // ***************************************************************************
  // Memory Access ("Stage")
  // ***************************************************************************

  // **** Connect to "dbus" ****
  always_comb
    begin: Conntect
      reg [15:0] sdata16;

      dbus.mConnect
        ( ID,                   // ID
          sdata16,              // sdata
          mem_ws,               // ws
          {2{rf[idec_rs]}},     // mdata
          // adr
          {8'h00, idec_mem_adr[7:1], 1'b0},
          // we
          {idec_mem_adr[0],~idec_mem_adr[0]} & {2{idec_mem_we}},
          // re
          {idec_mem_adr[0],~idec_mem_adr[0]} & {2{idec_mem_re}}
          );

      // - Connect 16-bit databus to 8-bit CPU -
      mem_data = ( idec_mem_adr[0] ) ? sdata16[15:8] : sdata16[7:0];
    end


  mPreAdrDecode_resp busproperty;
  always_comb
    begin: PreAdrDecode
      // verilator lint_off WIDTH
      busproperty = dbus.mPreAdrDecode( 0, idec_mem_adr );
      // verilator lint_on WIDTH
    end

endmodule // cpu
