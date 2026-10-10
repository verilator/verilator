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

// Clocking outputs drive input ports: the reproducer shape requires
// input-direction ports, so waive ASSIGNIN on the sender interfaces.
/* verilator lint_off ASSIGNIN */
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

interface select_sender_if (
    input wire clk,
    input wire enable,
    input wire strobe,
    input wire [11:0] bus
);
  clocking sender_cb @(posedge clk);
    default input #1step output #1step;
    input enable;
    output strobe;
    output bus;
  endclocking

  class select_driver;
    task drive(input logic [11:0] value);
      sender_cb.strobe <= 1'b1;
      sender_cb.bus <= value;
      @(sender_cb);
    endtask
  endclass

  select_driver driver = new;
endinterface
/* verilator lint_on ASSIGNIN */

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

// Array-select leaves: the driven data fans out through unpacked array
// element selects, including a variable index, plus a bit-select leaf.
interface select_harness_if (
    input wire clk,
    input wire enable,
    input wire strobe,
    input wire [3:0] words [0:1],
    input wire idx,
    input wire [7:0] vec
);
  select_sender_if sender (
      .clk(clk),
      .enable(enable),
      .strobe(strobe),
      .bus({words[1], words[idx], vec[7:4]})
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

module dut_select (
    input wire clk,
    output logic enable,
    input wire strobe,
    input wire [3:0] words [0:1],
    input wire idx,
    input wire [7:0] vec
);
  always_comb enable = 1'b1;
  bind dut_select select_harness_if harness (.*);
endmodule

module t;
  logic clk = 0;
  packet_t expected;
  packet_t got_direct;
  logic [3:0] exp_words [0:1];

  // DUT inputs are driven through the bound harnesses; the top-level
  // connections below are dummies that only satisfy pin connectivity.
  logic unused_enable1, unused_enable2, unused_enable3;
  logic unused_strobe1, unused_strobe2, unused_strobe3;
  logic [$bits(packet_t)-1:0] unused_bus1;
  logic unused_flag;
  logic [5:0] unused_id;
  logic [7:0] unused_value;
  logic [3:0] unused_words [0:1];
  logic unused_idx;
  logic [7:0] unused_vec;

  dut_direct direct_i (.clk(clk), .enable(unused_enable1), .strobe(unused_strobe1),
                       .bus(unused_bus1));
  dut_pattern pattern_i (.clk(clk), .enable(unused_enable2), .strobe(unused_strobe2),
                          .flag(unused_flag), .id(unused_id), .value(unused_value));
  dut_select select_i (.clk(clk), .enable(unused_enable3), .strobe(unused_strobe3),
                        .words(unused_words), .idx(unused_idx), .vec(unused_vec));

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

      @(posedge clk);
      #1;
      /* verilator lint_off ASSIGNIN */
      select_i.idx = (i & 1) != 0;
      select_i.vec = 8'((i * 17 + 9) & 255);
      /* verilator lint_on ASSIGNIN */
      select_i.harness.sender.driver.drive({expected[7:4], expected[3:0], select_i.vec[7:4]});
      #1;
      `checkd(select_i.strobe, 1'b1);
      // Connection leaf order is words[1] then words[idx]: the second write
      // wins when idx==1, so words[1] holds expected[7:4] only when idx==0.
      // The vec[7:4] bit-select leaf exercises AstSel handling.
      if (select_i.idx == 1'b0) begin
        exp_words[1] = expected[7:4];
        `checkd(select_i.words[1], exp_words[1]);
      end else begin
        exp_words[1] = expected[3:0];
        `checkd(select_i.words[1], exp_words[1]);
      end
      `checkd(select_i.vec, 8'((i * 17 + 9) & 255));
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
