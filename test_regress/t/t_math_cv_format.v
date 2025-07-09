// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   wire signed [21:10] out0;

   sub sub (
       .out0(out0)
   );

   sub2 sub2 ();

   string s;

   initial begin
      #20;
      // Bug with sformat, so can't just number-compare
      s = $sformatf("out0=%0d", out0);
      `checks(s, "out0=-12");
      if (out0 > 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub (out0);
   reg signed [27:20] reg_4;
   output wire [21:10] out0;

   initial begin
      #1;
      reg_4 = 0;
   end

   wire [11:0] w55;
   wire [11:0] w23;
   // verilator lint_off WIDTHEXPAND
   assign w55 = ~reg_4[20];
   // verilator lint_on WIDTHEXPAND
   assign { w23[3], w23[1:0] } = 3'h0;
   assign { w23[11:4], w23[2] } = { w55[11:4], w55[2] };
   assign out0 = w23;
endmodule

module sub2;
   reg [27:5] in0;
   reg [26:11] in1;
   wire [24:14] wire_0;
   wire [26:5] out1;
   wire w085;
   wire w082;
   wire [10:0] w092;
   wire [9:0] w028;

   string s;

   initial begin
      in0 = 6902127;
      in1 = 10000;
      #10;
      s = $sformatf("out0=%0d", out1);
      `checks(s, "out0=0");
   end

   assign w028 = ~ { 9'h000, in0[23] };
   assign w092[1] = 1'h0;
   assign { w092[10:2], w092[0] } = w028;
   assign wire_0 = w092;
   assign w082 = | wire_0[18:17];
   assign w085 = w082 ? in1[11] : 1'h0;
   assign out1 = { 21'h000000, w085 };
endmodule
