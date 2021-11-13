// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   reg [63:0] crc;
   reg [63:0] sum;

   reg [127:0] in;

   check #(48) check48 (.*);
   check #(31) check31 (.*);
   check #(32) check32 (.*);
   check #(63) check63 (.*);
   check #(64) check64 (.*);
   check #(96) check96 (.*);
   check #(128) check128 (.*);

   always_comb begin
      if (crc[2:0] == 0) in = '0;
      else if (crc[2:0] == 1) in = ~'0;
      else if (crc[2:0] == 2) in = 128'b1;
      else if (crc[2:0] == 3) in = ~ 128'b1;
      else begin
         in = {crc, crc};
         if (crc[3]) in[31:0] = '0;
         if (crc[4]) in[63:32] = '0;
         if (crc[5]) in[95:64] = '0;
         if (crc[6]) in[127:96] = '0;
         if (crc[7]) in[31:0] = ~'0;
         if (crc[8]) in[63:32] = ~'0;
         if (crc[9]) in[95:64] = ~'0;
         if (crc[10]) in[127:96] = ~'0;
      end
   end

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d in=%x\n", $time, cyc, in);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc == 99) begin
         `checkr(check48.sum, 14574057015683440.000000);
         `checkr(check31.sum, 114141374814.000000);
         `checkr(check32.sum, 236547942750.000000);
         `checkr(check63.sum, 513694866079917670400.000000);
         `checkr(check64.sum, 1002533584033221181440.000000);
         `checkr(check96.sum, 4377373669974269260279175970816.000000);
         `checkr(check128.sum, 18358899571808044815012294240949812330496.000000);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module check(/*AUTOARG*/
   // Inputs
   in, clk, cyc
   );
   parameter WIDTH = 128;
   input [127:0] in;

   wire [WIDTH-1:0] ci = in[WIDTH-1:0];
   wire signed [WIDTH-1:0] cis = in[WIDTH-1:0];

   real r;
   real rs;
   always_comb r = ci;
   always_comb rs = cis;

   input clk;
   input integer cyc;
   real          sum;

   always_ff @ (negedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] w%0d in=%h r=%f rs=%f sum=%f\n", $time, WIDTH, ci, r, rs, sum);
`endif
      if (cyc < 10) sum <= 0;
      else sum <= sum + r + rs;
   end
endmodule
