// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2018 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;
  reg [63:0] crc;
  reg [63:0] sum;

  // Take CRC data and apply to testblock inputs
  wire [31:0] in = crc[31:0];

  Test test (  /*AUTOINST*/
      // Inputs
      .clk(clk),
      .in(in[31:0])
  );

  Test2 test2 (  /*AUTOINST*/
      // Inputs
      .clk(clk),
      .in(in[31:0])
  );

  UnpackedSamples unpacked_samples(clk, in);

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      // Setup
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc < 10) begin
    end
    else if (cyc < 90) begin
    end
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module UnpackedSamples(input clk, input [31:0] in);
  typedef bit [14:0] ascending_t [3:1];
  bit [7:0] values[2];
  bit [7:0] previous[2];
  bit [7:0] previous2[2];
  ascending_t ascending;
  ascending_t previous_ascending;
  bit [6:0] matrix[1:0][4:6];
  bit [6:0] previous_matrix[1:0][4:6];
  logic [7:0] unchanged[2] = '{8'h11, 8'h22};
  int cycles = 0;
  bit seen_stable = 0;
  bit seen_changed = 0;

  always @(negedge clk) begin
    if (cycles % 2 == 0) begin
      values[0] = in[7:0];
      values[1] = in[15:8];
      ascending[3] = in[14:0];
      ascending[1] = in[29:15];
      matrix[(cycles / 2) % 2][4 + cycles % 3] = in[6:0];
    end
  end

  always @(posedge clk) begin
    cycles <= cycles + 1;
    previous <= values;
    previous2 <= previous;
    previous_ascending <= ascending;
    previous_matrix <= matrix;
    `checkh($past(values), previous)
    `checkh($past(values, 2), previous2)
    `checkh($past(ascending), previous_ascending)
    `checkh($past(matrix), previous_matrix)
    `checkh($sampled(values), values)
    `checkh($sampled(matrix), matrix)
    `checkh($stable(values), values == previous)
    `checkh($changed(values), values != previous)
    `checkh($stable(ascending), ascending == previous_ascending)
    `checkh($stable(matrix), matrix == previous_matrix)
    if ($stable(values)) seen_stable = 1;
    if ($changed(values)) seen_changed = 1;
    if (cycles == 90) begin
      `checkh(seen_stable, 1'b1)
      `checkh(seen_changed, 1'b1)
    end
  end

  assert property (@(posedge clk) $stable(unchanged)) else `stop;
  assert property (@(posedge clk) unchanged == $past(unchanged)) else `stop;
  assert property (@(posedge clk) $stable(values) == (values == previous)) else `stop;
  global clocking @(posedge clk);
  endclocking
  assert property (@(posedge clk) $past_gclk(values) == previous) else `stop;
  assert property (@(posedge clk) $stable_gclk(values) == (values == previous)) else `stop;
  assert property (@(posedge clk) $changed_gclk(values) == (values != previous)) else `stop;
  property matrix_stable(v);
    $stable(v) == (matrix == previous_matrix);
  endproperty
  assert property (@(posedge clk) matrix_stable(matrix)) else `stop;
endmodule

module Test (  /*AUTOARG*/
    // Inputs
    clk,
    in
);

  input clk;
  input [31:0] in;

  reg [31:0] dly0;
  reg [31:0] dly1;
  reg [31:0] dly2;
  reg [31:0] dly3;
  reg [31:0] dly0Inc;
  reg [31:0] dly1Inc;
  reg [31:0] dly2Inc;
  reg [31:0] dly3Inc;

  // If called in an assertion, sequence, or property, the appropriate clocking event.
  // Otherwise, if called in a disable condition or a clock expression in an assertion, sequence, or prop, explicit.
  // Otherwise, if called in an action block of an assertion, the leading clock of the assertion is used.
  // Otherwise, if called in a procedure, the inferred clock
  // Otherwise, default clocking

  always @(posedge clk) begin
    dly0 <= in;
    dly1 <= dly0;
    dly2 <= dly1;
    dly3 <= dly2;
    dly0Inc <= in + 1;
    dly1Inc <= dly0Inc;
    dly2Inc <= dly1Inc;
    dly3Inc <= dly2Inc;
    if ($time > 40) begin
      // $past(expression, ticks, expression, clocking)
      // In clock expression
      if (dly0 != $past(in)) $stop;
      if (dly0 != $past(in,)) $stop;
      if (dly1 != $past(in, 2)) $stop;
      if (dly1 != $past(in, 2,)) $stop;
      if (dly1 != $past(in, 2,,)) $stop;
      if (dly0Inc != $past(in + 1)) $stop;
      if (dly0Inc != $past(in + 1,)) $stop;
      if (dly1Inc != $past(in + 1, 2)) $stop;
      if (dly1Inc != $past(in + 1, 2,)) $stop;
      if (dly1Inc != $past(in + 1, 2,,)) $stop;
      // $sampled(expression) -> expression
      if (in != $sampled(in)) $stop;
    end
  end

  assert property (@(posedge clk) $time < 40 || dly0 == $past(in));
  assert property (@(posedge clk) $time < 40 || dly0Inc == $past(in + 1));

endmodule

module Test2 (  /*AUTOARG*/
    // Inputs
    clk,
    in
);

  input clk;
  input [31:0] in;

  reg [31:0] dly0;
  reg [31:0] dly1;

  always @(posedge clk) begin
    dly0 <= in;
    dly1 <= dly0;
  end

  default clocking @(posedge clk);
  endclocking
  assert property (@(posedge clk) $time < 40 || dly1 == $past(in, 2));

endmodule
