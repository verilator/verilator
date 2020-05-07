// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   localparam string SVEC [0:7] = '{"zero", "one", "two", "three", "four", "five", "six", "seven"};

   initial begin
      $display("%s", SVEC[3'd1]);
      $write("*-* All Finished *-*\n");
      $finish;
   end

   localparam string REGX [0:31] = '{"zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0/fp", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                                      "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"};

   function string regx (logic [5-1:0] r, bit abi=1'b0);
      regx = abi ? REGX[r] : $sformatf("x%0d", r);
   endfunction: regx

   function string dis32 (logic [32-1:0] op);
      casez (op)
        32'b0000_0000_0000_0000_0000_0000_0001_0011: dis32 = $sformatf("nop");
        32'b0000_0000_0000_0000_0100_0000_0011_0011: dis32 = $sformatf("-");
        32'b????_????_????_????_?000_????_?110_0111: dis32 = $sformatf("jalr  %s, 0x%03x (%s)",
                                                                       regx(op[5-1:0]), op[16-1:0], regx(op[5-1:0]));
        default: dis32 = "illegal";
      endcase
   endfunction: dis32

   always @(posedge clk) begin
      for (int unsigned i=0; i<32; i++)
        $display("REGX: %s", regx(i[4:0]));
      $display("OP: %s", dis32(32'h00000000));
      $finish();
   end

endmodule
