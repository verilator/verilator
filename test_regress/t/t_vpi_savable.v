// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Flops accessed via VPI beside combinational logic derived from them: a status
// net, a duplicate register, and a tree of unpacked arrays.

module t (
    input logic clk,
    output logic [31:0] ctrl_o
);

  localparam logic [9:0] A_CTRL = 10'h014;

  // Stimulus, stepped by cyc; the tree inputs change on the negedge, between clock edges
  logic [7:0] cyc = 8'h0;
  logic rst;
  logic bus_we = 1'b0;
  logic [9:0] bus_addr = 10'h3ff;
  logic [31:0] bus_wdata = '0;
  logic set_a = 1'b0;
  logic set_b = 1'b0;
  assign rst = cyc < 8'd2;

  always @(posedge clk) begin
    cyc <= cyc + 8'h1;
    if (cyc == 8'd20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always @(negedge clk) begin
    set_a <= cyc == 8'd12;
    case (cyc)
      8'd4: begin
        bus_wdata <= 32'ha5;
        bus_addr <= 10'h00b;
      end
      8'd5: begin
        bus_wdata <= 32'h5a;
        bus_addr <= 10'h004;
      end
      8'd6: begin
        bus_wdata <= 32'hff;
        bus_addr <= 10'h007;
      end
      8'd7: bus_addr <= 10'h3ff;
      8'd11: begin
        bus_we <= 1'b1;
        bus_wdata <= 32'h0c0c0004;
        bus_addr <= A_CTRL;
      end
      8'd12: begin
        bus_we <= 1'b0;
        bus_wdata <= 32'h3c;
        bus_addr <= 10'h3f5;
      end
      8'd13: begin
        bus_wdata <= 32'ha7;
        bus_addr <= 10'h3fa;
      end
      default: ;
    endcase
  end

  logic [31:0] ctrl_r;
  logic flag_a;
  logic flag_b;
  logic [7:0] cnt;
  logic [5:0] status;
  assign status = {flag_a, flag_b, cnt[3:0]};

  // Comb unpacked arrays built one element per continuous assign, read back through a
  // variable index
  localparam int LVL0 = 8;
  localparam int LVL1 = 4;

  logic [7:0] lvl0[0:LVL0 - 1];
  logic [7:0] lvl1[0:LVL1 - 1];
  logic [7:0] lvl2[0:1];
  logic [7:0] picked;

  for (genvar i = 0; i < LVL0; ++i) begin : g0
    assign lvl0[i] = bus_wdata[7:0] ^ (8'h13 * 8'(i)) ^ {4'b0, bus_addr[3:0]};
  end
  for (genvar i = 0; i < LVL1; ++i) begin : g1
    assign lvl1[i] = lvl0[2*i] | lvl0[(2*i)+1];
  end
  for (genvar i = 0; i < 2; ++i) begin : g2
    assign lvl2[i] = lvl1[2*i] & lvl1[(2*i)+1];
  end

  assign picked = lvl2[bus_addr[0]];

  assign ctrl_o = ctrl_r;
  wire [31:0] ctrl_dup = ctrl_r;

  always_ff @(posedge clk) begin
    if (rst) begin
      ctrl_r <= '0;
      flag_a <= 1'b0;
      flag_b <= 1'b0;
      cnt <= '0;
    end
    else begin
      flag_a <= flag_a | set_a;
      flag_b <= flag_b | set_b;
      cnt <= cnt + 8'h1;
      if (bus_we && bus_addr == A_CTRL) ctrl_r <= bus_wdata;
    end
  end

endmodule
