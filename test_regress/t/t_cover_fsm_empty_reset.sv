// DESCRIPTION: Verilator: FSM coverage ignores empty reset branches
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module two_proc_empty_reset (
    input logic clk,
    input logic rst,
    input logic go
);
  typedef enum logic {
    IDLE,
    BUSY
  } state_t;

  state_t state = IDLE;
  state_t state_next;

  always_ff @(posedge clk) begin
    if (rst) begin
    end
    else state <= state_next;
  end

  always_comb begin
    state_next = state;
    case (state)
      IDLE: state_next = go ? BUSY : IDLE;
      default: state_next = IDLE;
    endcase
  end
endmodule

module oneblock_empty_reset (
    input logic clk,
    input logic rst,
    input logic take_alt
);
  typedef enum logic [1:0] {
    WAITING,
    COLLECTING,
    SENDING
  } state_t;

  state_t state = WAITING;

  always_ff @(posedge clk) begin
    if (rst) begin
    end
    else
      case (state)
        WAITING: state <= take_alt ? SENDING : COLLECTING;
        COLLECTING: state <= SENDING;
        SENDING: state <= WAITING;
        default: state <= WAITING;
      endcase
  end
endmodule

module inline_empty_reset (
    input logic clk,
    input logic rst,
    input logic input_valid,
    input logic input_last,
    input logic output_ready,
    input logic [6:0] input_data,
    output logic [6:0] output_data,
    output logic output_valid
);
  typedef enum logic [1:0] {
    WAITING,
    COLLECTING,
    SENDING
  } state_t;

  state_t state = WAITING;
  logic [6:0] saved_data = '0;

  always_ff @(posedge clk) begin
    if (rst) begin
    end
    else if (state == WAITING) begin
      if (input_valid) begin
        saved_data <= input_data;
        state <= input_last ? SENDING : COLLECTING;
      end
      else begin
        state <= WAITING;
      end
    end
    else if (state == COLLECTING) begin
      if (input_valid && input_last) begin
        state <= SENDING;
      end
      else begin
        state <= COLLECTING;
      end
    end
    else if (state == SENDING) begin
      if (output_ready) begin
        state <= WAITING;
      end
      else begin
        state <= SENDING;
      end
    end
  end

  always_comb begin
    output_valid = state == SENDING;
    output_data = saved_data;
  end
endmodule

module t (
    input logic clk
);
  logic rst;
  logic go;
  logic take_alt;
  logic input_valid;
  logic input_last;
  logic output_ready;
  logic [6:0] input_data;
  logic [6:0] output_data;
  logic output_valid;
  int cyc;

  two_proc_empty_reset two_proc_u (
      .clk(clk),
      .rst(rst),
      .go(go)
  );

  oneblock_empty_reset oneblock_u (
      .clk(clk),
      .rst(rst),
      .take_alt(take_alt)
  );

  inline_empty_reset inline_u (
      .clk(clk),
      .rst(rst),
      .input_valid(input_valid),
      .input_last(input_last),
      .output_ready(output_ready),
      .input_data(input_data),
      .output_data(output_data),
      .output_valid(output_valid)
  );

  initial begin
    rst = 1'b1;
    go = 1'b0;
    take_alt = 1'b0;
    input_valid = 1'b0;
    input_last = 1'b0;
    output_ready = 1'b0;
    input_data = 7'h12;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      rst <= 1'b0;
      go <= 1'b1;
      take_alt <= 1'b0;
      input_valid <= 1'b1;
      input_last <= 1'b0;
    end
    if (cyc == 2) begin
      go <= 1'b0;
      input_valid <= 1'b1;
      input_last <= 1'b1;
      input_data <= 7'h35;
    end
    if (cyc == 3) begin
      input_valid <= 1'b0;
      output_ready <= 1'b1;
    end
    if (cyc == 4) begin
      output_ready <= 1'b0;
      take_alt <= 1'b1;
    end
    if (cyc == 7) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
