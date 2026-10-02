// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Martin Velay
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%p exp=%p\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc;
  logic [1:0] rx_int;
  wire [1:0] rx;
  bit drive_rx;
  assign rx = drive_rx ? rx_int : 'z;
endinterface

module t;
  logic [3:0][1:0] src = {2'd3, 2'd2, 2'd1, 2'd3};
  wire [3:0][1:0] observed;
  wire [2:1][3:2][1:0] nested;
  wire [3:0][1:0] array_observed;
  ifc array_if[3:0] ();

  for (genvar i = 0; i < 4; i++) begin : gen
    ifc u_if ();
    assign u_if.rx = src[i];
    assign observed[i] = u_if.rx;
    assign array_if[i].rx = src[i];
    assign array_observed[i] = array_if[i].rx;
  end
  for (genvar j = 1; j <= 2; j++) begin : outer
    for (genvar i = 2; i <= 3; i++) begin : inner
      ifc u_if ();
      assign u_if.rx = src[i-2] ^ 2'(j);
      assign nested[j][i] = u_if.rx;
    end
  end

  initial begin
    repeat (16) begin
      #1;
      `checkh(observed, src);
      `checkh(array_observed, src);
      for (int j = 1; j <= 2; j++) begin
        for (int i = 2; i <= 3; i++) begin
          `checkh(nested[j][i], src[i-2] ^ 2'(j));
        end
      end
      src = src + 8'h13;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
