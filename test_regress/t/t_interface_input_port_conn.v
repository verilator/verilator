// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Port connections to interface net-type input ports should not trigger
// ASSIGNIN. This is the port-connection counterpart to
// t_interface_input_port_assign which tests continuous assignments.

interface ifc_status (
    input wire busy
);
endinterface

module dut (
    output logic sleep_o
);
  initial sleep_o = 1'b1;
endmodule

module dut_wrap (
    ifc_status sif
);
  dut u_dut (
      .sleep_o(sif.busy)
  );
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;
  integer cyc = 0;

  ifc_status sif (.busy());

  dut_wrap u_wrap (.sif(sif));

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) begin
      `checkh(sif.busy, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
