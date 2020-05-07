// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define CONCAT(a, b) a``b
`define STRINGIFY(x) `"x`"

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;
   integer c_trace_on;

   sub sub ();

   // verilator tracing_off
   string  filename;
   // verilator tracing_on

   initial begin
`ifdef TEST_FST
      filename = {`STRINGIFY(`TEST_OBJ_DIR), "/simx.fst"};
`else
      filename = {`STRINGIFY(`TEST_OBJ_DIR), "/simx.vcd"};
`endif

`ifdef TEST_DUMP
      $dumpfile(filename);
      $dumpvars(0, top);
      $dumplimit(10 * 1024 * 1024);
`elsif TEST_DUMPPORTS
      $dumpports(top, filename);
      $dumpportslimit(10 * 1024 * 1024, filename);
`endif
   end

   always @ (posedge clk) begin
      if (cyc != 0) begin
         cyc <= cyc + 1;
         c_trace_on <= cyc + 2;
         if (cyc == 3) begin
`ifdef TEST_DUMP
            $dumpoff;
`elsif TEST_DUMPPORTS
            $dumpportsoff(filename);
`endif
         end
         else if (cyc == 5) begin
`ifdef TEST_DUMP
            $dumpall;
            $dumpflush;
`elsif TEST_DUMPPORTS
            $dumpportsall(filename);
            $dumpportsflush(filename);
`endif
         end
         else if (cyc == 7) begin
`ifdef TEST_DUMP
            $dumpon;
`elsif TEST_DUMPPORTS
            $dumpportson(filename);
`endif
         end
         else if (cyc == 10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module sub;
   integer inside_sub_a = 1;
endmodule
