// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module sub (
  input  wire        clock_4,
  input  wire        clock_8,
  output wire [28:5] out63
);

   reg [28:0]  reg_12;
   reg [28:22] reg_24;

   wire        _0558_ = | reg_24[26:25]; // reg_24 = 0 or 1100110 ---> _0558_ == 0
   wire [28:0] _0670_ = _0558_ ? reg_12 : 29'h00000f93; // _0558_ == 0 ---> _0670_ == 29'h00000f93
   wire [28:0] _0399_= - _0670_; // _0670_ == 29'h00000f93 ---> _0399_ = 29'b11111111111111111000001101101
   wire        _0085_ = ~ _0399_[2]; // _0399_[2] == 1 ---> _0085_ == 0
   wire [28:0] _0769_;
   assign { _0769_[28:3], _0769_[1:0] } = { _0399_[28:3], _0399_[1:0] }; // _0769_ != 0
   assign _0769_[2] = _0085_;

   // verilator lint_off WIDTH
   wire        _0305_ = ! _0769_; // _0769_ != 0 ---> _0305_ == 0
   wire [23:0] _0306_ = ! _0305_; // _0305_ == 0 ---> _0306_ == 1
   // verilator lint_on WIDTH

   assign out63  = _0306_; // out63 == 1

   always @(posedge clock_4, posedge clock_8)
     if (clock_8) reg_12 <= 29'h00000066;
     else reg_12 <= { reg_12[28:27], 25'h0000001, reg_12[1:0] };

   always @(posedge clock_4, posedge clock_8)
     if (clock_8) reg_24 <= 7'h66;
     else reg_24 <= reg_24;

endmodule

module t;
   reg  clock_4;
   reg  clock_8;
   wire signed [28:5] out63;
   reg signed [7:0] tmp = -1;
   reg signed [0:0] one = 1;
   reg signed [0:0] onert = 1;

   sub sub (
            .clock_4 (clock_4),
            .clock_8 (clock_8),
            .out63   (out63)
            );


   initial begin
      // All simulators agree: 1'sb1 really shows as decimal -1
      $display("one 'd=%d 'b=%b", one, one);
`ifdef VERILATOR
      onert = $c(1);
`endif
      $display("ort 'd=%d 'b=%b", onert, onert);

      $display("tmp 'd=%d 'b=%b", tmp, tmp);

      clock_4 = 0;
      clock_8 = 0;
      #2000;

      sub.reg_24 = 0;
      sub.reg_12 = 0;
      #2000;

      clock_4 = 0;
      clock_8 = 0;
      #10;
      $display("out63 'd=%d 'b=%b", out63, out63);

      #2000;
      clock_4 = 1;
      clock_8 = 1;
      #10;
      $display("out63 'd=%d 'b=%b", out63, out63);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
