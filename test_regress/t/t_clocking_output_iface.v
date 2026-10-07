// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// Clocking-block outputs driving a struct through a bound harness: direct
// vector passthrough versus struct assignment pattern fanout. The pattern
// variant loses the driven data.
// Note: each harness uses a distinct inner interface type so the class-based
// driver calls resolve to their own instance.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

typedef struct packed {
  logic flag;
  logic [5:0] id;
  logic [7:0] value;
} packet_t;

interface direct_sender_if (
    input wire clk,
    input wire enable,
    input wire strobe,
    input wire [$bits(packet_t)-1:0] bus
);
  clocking sender_cb @(posedge clk);
    default input #1step output #1step;
    input enable;
    output strobe;
    output bus;
  endclocking

  class direct_driver;
    task drive(input logic [$bits(packet_t)-1:0] value);
      sender_cb.strobe <= 1'b1;
      sender_cb.bus <= value;
      @(sender_cb);
    endtask
  endclass

  direct_driver driver = new;
endinterface

interface pattern_sender_if (
    input wire clk,
    input wire enable,
    input wire strobe,
    input wire [$bits(packet_t)-1:0] bus
);
  clocking sender_cb @(posedge clk);
    default input #1step output #1step;
    input enable;
    output strobe;
    output bus;
  endclocking

  class pattern_driver;
    task drive(input logic [$bits(packet_t)-1:0] value);
      sender_cb.strobe <= 1'b1;
      sender_cb.bus <= value;
      @(sender_cb);
    endtask
  endclass

  pattern_driver driver = new;
endinterface

// Control: struct crosses the harness boundary as one flat vector.
interface direct_harness_if (
    input wire clk,
    input wire enable,
    input wire strobe,
    input wire [$bits(packet_t)-1:0] bus
);
  direct_sender_if sender (.*);
endinterface

// Reproducer: struct is fanned out to sub-ports and reassembled with an
// assignment pattern in the port connection; the driven data is lost.
interface pattern_harness_if (
    input wire clk,
    input wire enable,
    input wire strobe,
    input wire flag,
    input wire [5:0] id,
    input wire [7:0] value
);
  pattern_sender_if sender (
      .clk(clk),
      .enable(enable),
      .strobe(strobe),
      .bus(packet_t'{
          flag: flag,
          id: id,
          value: value
      })
  );
endinterface

module dut_direct (
    input wire clk,
    output logic enable,
    input wire strobe,
    input wire [$bits(packet_t)-1:0] bus
);
  always_comb enable = 1'b1;
  bind dut_direct direct_harness_if harness (.*);
endmodule

module dut_pattern (
    input wire clk,
    output logic enable,
    input wire strobe,
    input wire flag,
    input wire [5:0] id,
    input wire [7:0] value
);
  always_comb enable = 1'b1;
  bind dut_pattern pattern_harness_if harness (.*);
endmodule

module t;
  logic clk = 0;
  packet_t expected;
  packet_t got_direct;

  dut_direct direct_i (.clk(clk));
  dut_pattern pattern_i (.clk(clk));

  always #5 clk = ~clk;

  initial begin
    for (int i = 0; i < 8; i++) begin
      expected = '{flag: (i & 1) != 0,
                   id: 6'((i * 7 + 3) & 63),
                   value: 8'((i * 13 + 5) & 255)};

      @(posedge clk);
      #1;
      direct_i.harness.sender.driver.drive(expected);
      #1;
      `checkd(direct_i.strobe, 1'b1);
      got_direct = packet_t'(direct_i.bus);
      `checkd(got_direct.flag, expected.flag);
      `checkd(got_direct.id, expected.id);
      `checkd(got_direct.value, expected.value);

      @(posedge clk);
      #1;
      pattern_i.harness.sender.driver.drive(expected);
      #1;
      `checkd(pattern_i.strobe, 1'b1);
      `checkd(pattern_i.flag, expected.flag);
      `checkd(pattern_i.id, expected.id);
      `checkd(pattern_i.value, expected.value);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
