// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Pawel Jewstafjew (Pawel.Jewstafjew@gmail.com).
// SPDX-License-Identifier: CC0-1.0

interface Iface (input bit [31:0] regs [1]);
   initial begin
      string instance_path = $sformatf("%m");
      $display("Iface path %s\n", instance_path);
      $write("*-* All Finished *-*\n");
      $finish;
   end

   bit [0:0] ppp;
   always_comb begin
      // Ok:
      //for (int index = 1 ; index < 2 ; ++index) begin
      foreach (regs[index]) begin
         ppp[index] = 1;
      end
   end

endinterface

module top (input bit [31:0] regs [1]);
   Iface t1(.regs(regs));
endmodule
