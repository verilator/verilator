// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,
               expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef bit bit_q_t[$];

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  // If validating this testbench in commercial simulator (it passes at time of PR)
  // you can generate your own clock rather than use Verilator's auto-argument clock.
  // logic clk;
  // initial clk = 0;
  // always #5 clk = ~clk;

  integer        cyc = 0;
  reg     [63:0] crc;
  reg     [63:0] sum;

  // Take CRC data and apply to testblock inputs
  wire    [31:0] in = crc[31:0];

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  wire    [31:0] out;  // From test of Test.v
  // End of automatics

  Test test (  /*AUTOINST*/
      // Outputs
      .out(out[31:0]),
      // Inputs
      .clk(clk),
      .in (in[31:0])
  );

  // Aggregate outputs into a single result vector
  wire [63:0] result = {32'h0, out};

  initial begin
    byte unsigned p[$];
    byte unsigned po[$];
    bit bits[$];
    string s;

    p = {8'h84, 8'haa};
    `checkh(p[0], 8'h84);
    `checkh(p[1], 8'haa);

    // The main thing this exercises which is not covered by t_stream_bitqueue.v
    // is the change in type values between 1-bit and 8-bit data, both of which
    // use CData type in the emitted C++. p is a queue of bytes, then the result
    // of the cast is a stream of bits, and then the outer left-stream does an
    // every-8-bits reordering and then the result is assigned to a bit queue.
    bits = {<<8{bit_q_t'({<<{p}})}};

    bits.push_front(1'b0);  // Shift

    // This is similar to the above except it assigns the result to a byte queue.
    po = {<<8{bit_q_t'({<<{bits}})}};

    // // Check the results of the above operations match expectations.
    s  = $sformatf("p=%p", p);
    `checks(s, "p='{'h84, 'haa} ");

    s = $sformatf("bits=%p", bits);
    `checks(s,
            "bits='{'h0, 'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1} ");

    // po inner bit-reversal would give bits of {1 | 0, 1, 0, 1, 0, 1, 0, 1 | 0, 0, 0, 0, 1, 0, 0, 0}
    // which then when reversed in 8-bit groups (as indicated) gives 8'h08, 8'h55, 8'h1, but since that
    // doesn't agree with other simulators, they must pad 8'h1 on the right with zeros to give the rightmost
    // 8'80? This doesn't make any sense.
    s = $sformatf("po=%p", po);
    `checks(s, "po='{'h8, 'h55, 'h80} ");

    // TODO: remove this
    $write("*-* All Finished *-*\n");
    $finish;
  end


  // TODO: uncomment this
  //   always @(posedge clk) begin
  // `ifdef TEST_VERBOSE
  //     $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
  // `endif
  //     cyc <= cyc + 1;
  //     crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
  //     sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
  //     if (cyc == 0) begin
  //       // Setup
  //       crc <= 64'h5aef0c8d_d70a4497;
  //       sum <= '0;
  //     end else if (cyc < 10) begin
  //       sum <= '0;
  //     end else if (cyc == 99) begin
  //       $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
  //       if (crc !== 64'hc77bb9b3784ea091) $stop;
  //       // What checksum will we end up with (above print should match)
  //       `define EXPECTED_SUM 64'h9721d4e989defb24
  //       `checkh(sum, `EXPECTED_SUM);
  //       $write("*-* All Finished *-*\n");
  //       $finish;
  //     end
  //   end

endmodule

module Test (  /*AUTOARG*/
    // Outputs
    out,
    // Inputs
    clk,
    in
);
  input clk;
  input [31:0] in;
  output reg [31:0] out;

  always_ff @(posedge clk) begin
    byte unsigned p[$];
    byte unsigned po[$];
    bit bits[$];
    p = {in[31:24], in[23:16], in[15:8], in[7:0]};
    // Convert 'p' byte stream into byte-opposite queue bit-stream
    bits = {<<8{bit_q_t'({<<{p}})}};
    bits.push_front(1'b0);  // Shift
    po  = {<<8{bit_q_t'({<<{bits}})}};
    out = {po[3], po[2], po[1], po[0]};
  end
endmodule
