// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef USE_INLINE
 `define INLINE_MODULE /*verilator inline_module*/
`else
 `define INLINE_MODULE /*verilator public_module*/
`endif

module t (/*AUTOARG*/);

`define DRAM1(bank) mem.mem_bank[bank].dccm.dccm_bank.ram_core
`define DRAM2(bank) mem.mem_bank2[bank].dccm.dccm_bank.ram_core
`define DRAM3(bank) mem.mem_bank3[bank].dccm.dccm_bank.ram_core
`define DRAM4(bank) mem.sub4.mem_bank4[bank].dccm.dccm_bank.ram_core

   initial begin
      `DRAM1(0)[3] = 130;
      `DRAM1(1)[3] = 131;
      `DRAM2(0)[3] = 230;
      `DRAM2(1)[3] = 231;
      `DRAM3(0)[3] = 330;
      `DRAM3(1)[3] = 331;
      `DRAM4(0)[3] = 430;
      `DRAM4(1)[3] = 431;
      if (`DRAM1(0)[3] !== 130) $stop;
      if (`DRAM1(1)[3] !== 131) $stop;
      if (`DRAM2(0)[3] !== 230) $stop;
      if (`DRAM2(1)[3] !== 231) $stop;
      if (`DRAM3(0)[3] !== 330) $stop;
      if (`DRAM3(1)[3] !== 331) $stop;
      if (`DRAM4(0)[3] !== 430) $stop;
      if (`DRAM4(1)[3] !== 431) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   eh2_lsu_dccm_mem mem (/*AUTOINST*/);

endmodule

module eh2_lsu_dccm_mem
#(
  DCCM_INDEX_DEPTH = 8192,
  DCCM_NUM_BANKS = 2
 )(
);
   `INLINE_MODULE

   // 8 Banks, 16KB each (2048 x 72)
   for (genvar i=0; i<DCCM_NUM_BANKS; i++) begin: mem_bank
      if (DCCM_INDEX_DEPTH == 16384) begin : dccm
         eh2_ram
           #(.depth(16384), .width(32))
         dccm_bank (.*);
      end
      else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
         eh2_ram
           #(.depth(8192), .width(32))
         dccm_bank (.*);
      end
      else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
         eh2_ram
           #(.depth(4096), .width(32))
         dccm_bank (.*);
      end
   end : mem_bank

   // Check that generate doesn't also add a genblk
   generate
      for (genvar i=0; i<DCCM_NUM_BANKS; i++) begin: mem_bank2
         if (DCCM_INDEX_DEPTH == 8192) begin : dccm
            eh2_ram
              #(.depth(8192), .width(32))
            dccm_bank (.*);
         end
      end
   endgenerate

   // Nor this
   generate
      begin
         for (genvar i=0; i<DCCM_NUM_BANKS; i++) begin: mem_bank3
            if (DCCM_INDEX_DEPTH == 8192) begin : dccm
               eh2_ram
                 #(.depth(8192), .width(32))
               dccm_bank (.*);
            end
         end
      end
   endgenerate

   // This does
   generate
      begin : sub4
         for (genvar i=0; i<DCCM_NUM_BANKS; i++) begin: mem_bank4
            if (DCCM_INDEX_DEPTH == 8192) begin : dccm
               eh2_ram
                 #(.depth(8192), .width(32))
               dccm_bank (.*);
            end
         end
      end
   endgenerate

   // This is an error (previously declared)
   //generate
   //   begin
   //      eh2_ram
   //      #(.depth(8192), .width(32))
   //    dccm_bank (.*);
   //   end
   //   begin
   //      eh2_ram
   //      #(.depth(8192), .width(32))
   //    dccm_bank (.*);
   //   end
   //endgenerate

endmodule

module eh2_ram #(depth=4096, width=39)
   ();

   `INLINE_MODULE

   reg [(width-1):0] ram_core [(depth-1):0];

endmodule
