// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// A virtual handle to the bound harness keeps its port connections from being
// aliased. Two instances of one interface type play different roles: a sender
// whose clocking outputs drive the DUT inputs, and a monitor whose clocking
// inputs sample the DUT outputs. Both connect through a struct assignment pattern.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  logic flag;
  logic [7:0] value;
} packet_t;

/* verilator lint_off ASSIGNIN */
interface channel_if (
    input wire clk,
    input wire valid,
    input wire [$bits(packet_t)-1:0] data
);
  clocking mon_cb @(posedge clk);
    default input #1step output #1step;
    input valid;
    input data;
  endclocking

  clocking drv_cb @(posedge clk);
    default input #1step output #1step;
    output valid;
    output data;
  endclocking

  class driver;
    task drive(input packet_t item);
      drv_cb.valid <= 1'b1;
      drv_cb.data <= item;
      @(drv_cb);
    endtask
  endclass

  driver drv = new;
endinterface
/* verilator lint_on ASSIGNIN */

interface harness_if (
    input wire clk,
    input wire in_valid,
    input wire in_flag,
    input wire [7:0] in_value,
    input wire out_valid,
    input wire out_flag,
    input wire [7:0] out_value
);
  channel_if in_ch (
      .clk(clk),
      .valid(in_valid),
      .data(packet_t'{flag: in_flag, value: in_value})
  );

  channel_if out_ch (
      .clk(clk),
      .valid(out_valid),
      .data(packet_t'{flag: out_flag, value: out_value})
  );

  function logic get_in_valid();
    return in_valid;
  endfunction

  function logic get_out_valid();
    return out_ch.mon_cb.valid;
  endfunction

  function packet_t get_out_data();
    return packet_t'(out_ch.mon_cb.data);
  endfunction
endinterface

module dut (
    input wire clk,
    input wire in_valid,
    input wire in_flag,
    input wire [7:0] in_value,
    output logic seen_valid,
    output packet_t seen_data,
    output logic out_valid,
    output logic out_flag,
    output logic [7:0] out_value
);
  always_comb begin
    seen_valid = in_valid;
    seen_data = packet_t'{flag: in_flag, value: in_value};
    out_valid = 1'b1;
    out_flag = 1'b1;
    out_value = 8'ha5;
  end

  bind dut harness_if harness (.*);
endmodule

module t;
  logic clk = 1'b0;
  logic seen_valid;
  packet_t seen_data;
  packet_t exp_in;
  packet_t exp_out;
  virtual harness_if vif;

  // DUT inputs are left unconnected: the bound harness drives them via in_ch
  dut dut_i (
      .clk(clk),
      .in_valid(),
      .in_flag(),
      .in_value(),
      .seen_valid(seen_valid),
      .seen_data(seen_data),
      .out_valid(),
      .out_flag(),
      .out_value()
  );

  always #5 clk = ~clk;

  initial begin
    vif = dut_i.harness;
    exp_in = '{flag: 1'b1, value: 8'h5a};
    exp_out = '{flag: 1'b1, value: 8'ha5};

    // Monitor: DUT outputs reach the clocking inputs of out_ch
    @(posedge clk);
    #1;
    `checkd(vif.get_out_valid(), 1'b1);
    `checkd(vif.get_out_data().flag, exp_out.flag);
    `checkd(vif.get_out_data().value, exp_out.value);

    // Sender: clocking outputs of in_ch reach the DUT inputs. The #1step output
    // skew applies the drive just after the clock edge, so check half a cycle later
    dut_i.harness.in_ch.drv.drive(exp_in);
    @(negedge clk);
    `checkd(vif.get_in_valid(), 1'b1);
    `checkd(seen_valid, 1'b1);
    `checkd(seen_data.flag, exp_in.flag);
    `checkd(seen_data.value, exp_in.value);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
