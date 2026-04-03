// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface sub_if (
    output reg [7:0] data
);
endinterface

interface top_if (
    output reg [7:0] data_out
);
  sub_if sub (.data(data_out));
endinterface

package pkg;
  typedef virtual top_if top_vif_t;
  typedef virtual sub_if sub_vif_t;

  class agent_c;
    top_vif_t vif;
  endclass

  class driver_c;
    top_vif_t vif;
    sub_vif_t sub_vif;

    // Sub-interface select from virtual interface
    function void assign_sub_vif(agent_c a);
      sub_vif = a.vif.sub;
    endfunction

    // Chained member access through sub-interface
    function void write_data(logic [7:0] val);
      vif.sub.data = val;
    endfunction

    // Read through chained sub-interface access
    function logic [7:0] read_data();
      return vif.sub.data;
    endfunction
  endclass
endpackage

module t;
  logic [7:0] wire_data;
  top_if tif (.data_out(wire_data));

  initial begin
    automatic pkg::agent_c a = new;
    automatic pkg::driver_c d = new;

    // Bind virtual interfaces
    a.vif = tif;
    d.vif = tif;

    // Test 1: Sub-interface select from virtual interface
    d.assign_sub_vif(a);

    // Test 2: Write through chained sub-interface access
    d.write_data(8'hA5);
    `checkd(wire_data, 8'hA5)

    // Test 3: Read through chained sub-interface access
    `checkd(d.read_data(), 8'hA5)

    // Test 4: Direct sub-interface member write
    d.sub_vif.data = 8'h3C;
    `checkd(wire_data, 8'h3C)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
