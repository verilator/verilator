// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Two instances of the same submodule with a multi-dim iface-array port.
// Exercises the subsequent-instance path in V3Inst::visit(AstPin) multi-dim:
// the first instance de-arrays sink's port var and unlinks it; the second
// instance finds pinVarp already unlinked and reuses the per-element vars
// cached in m_deModVars.

interface simple_if;
  logic [7:0] data;
endinterface

module sink (simple_if b [1:0][2:0]);
  logic [7:0] chk [1:0][2:0];
  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_a
      for (gj = 0; gj < 3; gj++) begin : g_b
        always_comb chk[gi][gj] = b[gi][gj].data;
      end
    end
  endgenerate
endmodule

module t;
  simple_if bus1 [1:0][2:0] ();
  simple_if bus2 [1:0][2:0] ();
  sink inst1 (.b(bus1));
  sink inst2 (.b(bus2));

  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_drive_a
      for (gj = 0; gj < 3; gj++) begin : g_drive_b
        initial begin
          bus1[gi][gj].data = 8'(gi * 3 + gj + 1);
          bus2[gi][gj].data = 8'(gi * 3 + gj + 100);
        end
      end
    end
  endgenerate

  initial begin
    #1;
    if (inst1.chk[0][0] !== 8'd1) begin $write("%%Error inst1[0][0]=%0d\n", inst1.chk[0][0]); $stop; end
    if (inst1.chk[0][1] !== 8'd2) begin $write("%%Error inst1[0][1]=%0d\n", inst1.chk[0][1]); $stop; end
    if (inst1.chk[0][2] !== 8'd3) begin $write("%%Error inst1[0][2]=%0d\n", inst1.chk[0][2]); $stop; end
    if (inst1.chk[1][0] !== 8'd4) begin $write("%%Error inst1[1][0]=%0d\n", inst1.chk[1][0]); $stop; end
    if (inst1.chk[1][1] !== 8'd5) begin $write("%%Error inst1[1][1]=%0d\n", inst1.chk[1][1]); $stop; end
    if (inst1.chk[1][2] !== 8'd6) begin $write("%%Error inst1[1][2]=%0d\n", inst1.chk[1][2]); $stop; end
    if (inst2.chk[0][0] !== 8'd100) begin $write("%%Error inst2[0][0]=%0d\n", inst2.chk[0][0]); $stop; end
    if (inst2.chk[0][1] !== 8'd101) begin $write("%%Error inst2[0][1]=%0d\n", inst2.chk[0][1]); $stop; end
    if (inst2.chk[0][2] !== 8'd102) begin $write("%%Error inst2[0][2]=%0d\n", inst2.chk[0][2]); $stop; end
    if (inst2.chk[1][0] !== 8'd103) begin $write("%%Error inst2[1][0]=%0d\n", inst2.chk[1][0]); $stop; end
    if (inst2.chk[1][1] !== 8'd104) begin $write("%%Error inst2[1][1]=%0d\n", inst2.chk[1][1]); $stop; end
    if (inst2.chk[1][2] !== 8'd105) begin $write("%%Error inst2[1][2]=%0d\n", inst2.chk[1][2]); $stop; end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
