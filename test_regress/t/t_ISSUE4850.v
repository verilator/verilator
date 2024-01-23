// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Swirhun.
// SPDX-License-Identifier: CC0-1.0

//
// Demonstrates the bug in https://github.com/verilator/verilator/issues/4850
//
// Specifically, _vl_insert_WI() writes to lword and hword when lword != hword
// may be unsafe, because (for example), lword was the highest valid place to
// perform a write and hword is out-of-bounds (and will in fact clobber other
// state in the generated C++ struct!).
//


module t(/*AUTOARG*/
   // Inputs
   clk,
   reset
   );
   input clk;
   input reset;

   integer cyc = 13;

   // These need to be generated/consumed in this testbench so that
   // they do not get pruned away when verilated
   logic insert = '0;
   logic [3:0] used, free;
   logic [95:0] data;

   always_ff @(posedge clk) begin
      if (reset) begin
         insert <= '0;
         cyc <= 32;
      end else begin
         insert <= '1;
         cyc <= cyc - 1;
      end

      $write("used [4'd%2d], free [4'd%2d], data[8+:4] = [32'h%08x]\n", used, free, data);

      if (used + free != 12) begin
         $write("used [4'd%2d] + free [4'd%2d] != 4'd12\n", used, free);
         $stop();
      end
      if (used == 0) begin
         $write("used [4'd%2d] was clobbered (should always be nonzero).\n", used);
         $stop();
      end
      if (cyc == 0) begin
         if (used == 12 && free == 0) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $write("used [4'd%2d] != 12 or free [4'd%2d] != 0\n", used, free);
            $stop();
         end
      end
   end

   dut dut_i(
      .clk(clk),
      .insert(insert),
      .used(used),
      .free(free),
      .data(data)
   );

endmodule

module dut(
   input logic clk,
   input logic insert,
   output logic [3:0] used,
   output logic [3:0] free,
   output logic [95:0] data
   );

   // This declaration order matters -- the fact that d_data is *before* d_used/d_free
   // means that with the existing bug, writes to d_data that extend beyond its length
   // will overwrite other fields in the state struct -- basically an "unsafe writes"
   // problem because the existing code wrote beyond the end of the array d_data.
   logic [11:0][7:0] d_data, d_data_next;
   logic [3:0] d_used = 4'd1, d_free = 4'd11, d_used_next;
   assign used = d_used;
   assign free = d_free;
   assign data = d_data;

   always_ff @(posedge clk) begin
      d_data <= d_data_next;
      d_used <= d_used_next;
      d_free <= 12 - d_used_next;
   end

   always_comb begin
    d_data_next = d_data;
    d_used_next = d_used;

    if ((insert == 1'b1) && (d_free >= {3'b0, insert})) begin
      // This write to d_data would clobber d_used before the issue was fixed
      d_data_next[d_used+:4] = 32'd0;
      d_used_next += 4'd1;
    end
  end
endmodule
