// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;


  int         cyc;
  reg  [63:0] crc;
  reg  [63:0] sum;

  // Values to swap and locations for the swapped values.
  wire [31:0] x_fwd = crc[31:0];
  wire [31:0] y_fwd;
  wire [31:0] x_bwd;
  wire [31:0] y_bwd = crc[63:32];

  Test test1 (
      .a(x_fwd),
      .b(y_fwd)
  );

  Test test2 (
      .a(x_bwd),
      .b(y_bwd)
  );

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d crc=%x x_fwd=%x y_bwd=%x\n", $time, cyc, crc, x_fwd, y_bwd);
`endif
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    sum <= {x_fwd, y_bwd} ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
      sum <= '0;
    end else if (cyc < 10) begin
      sum <= '0;
    end else
    if (cyc < 90) begin
    end else if (cyc == 99) begin
      $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
      `checkh(crc, 64'hc77bb9b3784ea091);
      // What checksum will we end up with (above print should match)
      `checkh(sum, 64'h5a3868140accd91d);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

// Swap the byte order of two args.
module Test (
    inout wire [31:0] a,
    inout wire [31:0] b
);

  alias {a[7:0], a[15:8], a[23:16], a[31:24]} = b;

  // Equivalent to

  // wire [31:0] a_prime;
  // wire [31:0] b_prime;

  // assign b_prime = {a[7:0],a[15:8],a[23:16],a[31:24]};
  // assign {a_prime[7:0],a_prime[15:8],a_prime[23:16],a_prime[31:24]} = b;
  // assign b = b_prime;
  // assign a = a_prime;
endmodule
