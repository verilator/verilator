// DESCRIPTION: Verilator: Verilog Test module
//
// When compiled using -fsanitize=address,undefined this triggered:
//
//   verilated_trace_imp.h:875:5: runtime error: store to misaligned address ...
//   verilated_trace.h:450:31: runtime error: load of misaligned address ...
//
// due to 32 bit aligned addresses being used for types which require
// stricter alignment.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by John Wehle.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;

  wire [2:0] out;
  reg        in;
  reg [39:0] p;
  reg        rst;
  reg        clk;

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0, test);

    clk = 0;
    rst = 0;

    for (int i = 0; i < 2; i++)
      begin
        #10 rst = 1;
        #10 rst = 0;

        p = 40'b0000000000111111111111111111110000000000;

        in = i[0];

        for (int k = 0; k < 31; k++)
          begin
            in = p[39 - k] ^ i[0];
            #1;
          end

        end

    #30 $write("*-* All Finished *-*\n");
    $finish;
  end

  always begin
    #10 clk <= !clk;
  end

  Test test(.out(out), .in(in),
	    .clk(clk), .rst(rst));
endmodule


module Test(/*AUTOARG*/
  // Outputs
  out,
  // Inputs
  clk, in, rst
  );

  input             clk;
  input             in;
  input             rst;
  output wire [2:0] out;

  reg [2:0] s;
  reg       sin;

  assign out = s;

  always @(posedge clk, posedge rst)
    begin
      s[0] <= s[2];
      s[2] <= in;
      s[1] <= sin;
    end

  always @(negedge clk, posedge rst)
    if (rst)
      sin <= 1'b0;
    else
      sin <= in;

endmodule
