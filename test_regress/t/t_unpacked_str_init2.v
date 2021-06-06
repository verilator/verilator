// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// issue2895

module t (/*AUTOARG*/);

   localparam string REG_X [0:31] = '{"zero", "ra", "sp", "gp", "tp", "t0",
                                      "t1", "t2", "s0/fp", "s1", "a0", "a1",
                                      "a2", "a3", "a4", "a5", "a6", "a7", "s2",
                                      "s3", "s4", "s5", "s6", "s7", "s8", "s9",
                                      "s10", "s11", "t3", "t4", "t5", "t6"};

   function string reg_x (logic [4:0] r, bit abi=1'b0);
      reg_x = abi ? REG_X[r] : $sformatf("x%0d", r);
   endfunction

   // the issue is triggered by a second function containing a case statement
   function string f2 (logic [4:0] r, bit abi=0);
      case (r)
        5'd0:    f2 = $sformatf("nop");
        5'd1:    f2 = $sformatf("reg %s", reg_x(r[4:0], abi));
        default: f2 = $sformatf("ILLEGAL");
      endcase
   endfunction

   initial begin
      for (int unsigned i = 0; i < 32; ++i) begin
         $display("REGX: %s", reg_x(i[4:0], 1'b1));
      end
      $display("OP: %s", f2(5'd7));
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
