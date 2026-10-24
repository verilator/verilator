// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%p exp=%p\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
`define check_array(a) \
  foreach (a[i]) begin \
    if (mode == 0) `checkh(a[i], '0); \
    else if (mode == 1) `checkh(a[i], '1); \
    else `checkh(a[i], a[$low(a)]); \
  end
// verilog_format: on

class ResetState;
  typedef logic [94:0] wide_t;
  wide_t values[3:1];
  logic [14:0] small_values[4:8];
endclass

module reset_child;
  typedef logic [64:0] wide_t;
  typedef struct packed {
    logic [6:0] flags;
    logic [57:0] payload;
  } packet_t;
  typedef enum logic [6:0] {
    IDLE = 7'd0,
    READY = 7'd127
  } state_t;
  logic [6:0] bytes[3:1];
  logic [14:0] shorts[2:6];
  logic [30:0] words[0:16];
  logic [32:0] longs[7:3];
  logic [62:0] singleton[4:4];
  wide_t wide[5:1];
  logic [94:0] wider[0:8];
  logic [128:0] widest[0:2];
  logic [128:0] lone_wide[2:2];
  packet_t packets[3:1];
  state_t states[2:6];
  wide_t matrix[3:1][2:6];
  bit [30:0] two_state[0:4];
  ResetState state;
  int mode;

  initial begin
    if (!$value$plusargs("mode=%d", mode)) `stop;
    `check_array(bytes);
    `check_array(shorts);
    `check_array(words);
    `check_array(longs);
    `check_array(singleton);
    `check_array(wide);
    `check_array(wider);
    `check_array(widest);
    `check_array(lone_wide);
    `check_array(packets);
    `check_array(states);
    foreach (matrix[i, j]) begin
      if (mode == 0) `checkh(matrix[i][j], '0);
      else if (mode == 1) `checkh(matrix[i][j], '1);
      else `checkh(matrix[i][j], matrix[1][2]);
    end
    foreach (two_state[i]) `checkh(two_state[i], 0);
    state = new;
    `check_array(state.values);
    `check_array(state.small_values);
  end
endmodule

module t (
    input clk
);
  reset_child a ();
  reset_child b ();
  always @(posedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
