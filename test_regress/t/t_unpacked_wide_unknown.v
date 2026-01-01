// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
  logic [149:0] hdr;
  logic [1:0] vc;
} packet_t;

module t;

  logic clk;

  typedef struct {packet_t [1:0] pkt_i;} dut_if_t;

  dut_if_t dut[2];

  initial begin
    clk = 0;
    forever #(0.5) clk = ~clk;
  end

  task automatic send_req_packets(int module_id, int channel);
    packet_t packet = '0;
    dut[module_id].pkt_i[channel] = packet;
    @(posedge clk);  // If you comment out this line. It will build.
  endtask

  initial begin
    for (int m = 0; m < 2; m++) begin
      for (int i = 0; i < 2; i++) begin
        automatic int mod = m;
        automatic int ch = i;
        send_req_packets(mod, ch);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
