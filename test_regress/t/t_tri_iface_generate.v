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

interface proc_ifc;
  logic [1:0] d;
endinterface

module t;
  logic [3:0][1:0] src = {2'd3, 2'd2, 2'd1, 2'd3};
  wire [3:0][1:0] observed;
  wire [2:1][3:2][1:0] nested;
  wire [3:0][1:0] array_observed;
  wire [3:0][1:0] proc_observed;
  wire [3:0][1:0] out_observed;
  wire [1:0] scoped_observed;
  wire [1:0] flat_observed;
  ifc array_if[3:0] ();
  proc_ifc blk_if ();
  proc_ifc self_if ();
  proc_ifc out_if[3:0] ();
  ifc g_u_if ();

  // The later write in a process wins, also from another named block
  always @* begin
    begin : first
      blk_if.d = src[0][0] ? src[2] : 'z;
      t.self_if.d = src[0][1] ? ~src[3] : 'z;
    end
    begin : second
      blk_if.d = ~src[2];
      t.self_if.d = src[3];
    end
  end

  for (genvar i = 0; i < 4; i++) begin : gen
    ifc u_if ();
    proc_ifc p_if ();
    assign u_if.rx = src[i];
    assign observed[i] = u_if.rx;
    assign array_if[i].rx = src[i];
    assign array_observed[i] = array_if[i].rx;
    always @* begin
      begin : first
        p_if.d = src[i][0] ? src[i] : 'z;
        out_if[i].d = src[i][1] ? src[3-i] : 'z;
        begin : inner
          p_if.d = src[i][1] ? ~src[i] : 'z;
        end
      end
      begin : second
        gen[i].p_if.d = src[i] ^ 2'(i);
        out_if[i].d = ~src[3-i];
      end
    end
    assign proc_observed[i] = p_if.d;
    assign out_observed[i] = out_if[i].d;
  end
  // A generated u_if and a module-level g_u_if are different instances
  if (1) begin : g
    ifc u_if ();
    assign u_if.rx = src[1][0] ? src[2] : 'z;
  end
  assign g_u_if.rx = src[1][0] ? ~src[2] : 'z;
  assign scoped_observed = g.u_if.rx;
  assign flat_observed = g_u_if.rx;

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
      `checkh(blk_if.d, ~src[2]);
      `checkh(self_if.d, src[3]);
      for (int i = 0; i < 4; i++) begin
        `checkh(proc_observed[i], src[i] ^ 2'(i));
        `checkh(out_observed[i], ~src[3-i]);
      end
      if (src[1][0]) begin
        `checkh(scoped_observed, src[2]);
        `checkh(flat_observed, ~src[2]);
      end
      src = src + 8'h13;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
