// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  bit clk = 1'b0;
  always #5 clk = ~clk;

  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  localparam N = 16;

  // Generate variables
  for (genvar n = 0; n < N; ++n) begin : vars
    logic [n:0] tmp;
    logic out;
  end

  // Generate logic
  for (genvar n = 0; n < N; ++n) begin
    if (n == 0) begin
      assign vars[n].tmp = ~crc[n];
      assign vars[n].out = vars[n].tmp[n];
    end
    else begin
      assign vars[n].tmp = {~crc[n], vars[n-1].tmp};
      assign vars[n].out = vars[n].tmp[n] ^ vars[n-1].out;
    end
  end

  // Would create cycle:
  wire [3:0] danger_src = {crc[4:3], crc[1:0]};
  wire [1:0] danger_sel = danger_src[2:1];
  wire [5:0] danger_dst = {~danger_sel, danger_src};

  // Sink has no other sinks
  wire [3:0] noother_src = {crc[5:4], crc[2:1]};
  wire [1:0] noother_sel = noother_src[2:1];
  wire [7:0] noother_dst = {crc[9:6], noother_src};  // singal intentianally unused

  int cyc;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    //$display("%16b %16b", ~crc[N-1:0], vars[N-1].tmp);
    //$display("%16b %16b", ^(~crc[N-1:0]), vars[N-1].out);
    // Check halfway through, this prevents pushing sels past this point
    `checkh(vars[N/2].tmp, ~crc[N/2:0]);
    `checkh(vars[N/2].out, ^(~crc[N/2:0]));
    // Check final value
    `checkh(vars[N-1].tmp, ~crc[N-1:0]);
    `checkh(vars[N-1].out, ^(~crc[N-1:0]));
    if (cyc == 10) begin
      // Observe danger_dst so it's not eliminated
      $display("%0b", danger_dst);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
