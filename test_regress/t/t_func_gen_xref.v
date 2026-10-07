// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc #(
    parameter int ID = 0
) ();
  int x = ID * 1000;
endinterface

module sub #(
    parameter int ID = 0
) ();
  int x = ID * 100;
endmodule

module mid #(
    parameter int ID = 0
) ();
  logic [7:0] mem[4] = '{
      8'(ID * 16 + 0),
      8'(ID * 16 + 1),
      8'(ID * 16 + 2),
      8'(ID * 16 + 3)
  };
  sub #(.ID(ID)) u_sub ();
  function automatic logic [7:0] rd(input int a);
    return mem[a];
  endfunction
  task automatic rdTask(input int a, output logic [7:0] o);
    o = mem[a];
  endtask
  if (1) begin : g_in
    function automatic int id();
      return ID;
    endfunction
  end
endmodule

module top;
  for (genvar w = 1; w <= 2; w++) begin : g_way
    mid #(.ID(w)) u_mid ();
    ifc #(.ID(w)) u_ifc ();
    // Hierarchical references to a sub-instance from a function in the same generate block
    function automatic logic [7:0] rdFunc(input int a);
      return u_mid.rd(a);
    endfunction
    function automatic logic [7:0] rdVar(input int a);
      return u_mid.mem[a];
    endfunction
    function automatic void wrVar(input int a, input logic [7:0] d);
      u_mid.mem[a] = d;
    endfunction
    task automatic rdTask(input int a, output logic [7:0] o);
      u_mid.rdTask(a, o);
    endtask
    function automatic int rdSub();
      return u_mid.u_sub.x;
    endfunction
    function automatic int rdGen();
      return u_mid.g_in.id();
    endfunction
    function automatic int rdIfc();
      return u_ifc.x;
    endfunction
    // Hierarchical references through the generate block itself, and absolute
    function automatic logic [7:0] rdSelf(input int a);
      return g_way[w].u_mid.rd(a);
    endfunction
    function automatic logic [7:0] rdAbs(input int a);
      return top.g_way[w].u_mid.rd(a);
    endfunction
    // Static function with a named block inside
    function logic [7:0] rdBlock(input int a);
      static logic [7:0] cnt = 0;
      begin : blk
        cnt++;
        return u_mid.rd(a) + cnt;
      end
    endfunction
    // Nested generate block with its own instance of the same name
    if (1) begin : g_inner
      mid #(.ID(w + 4)) u_mid ();
      function automatic logic [7:0] rdInner(input int a);
        return u_mid.rd(a);
      endfunction
    end
    // Nested generate block referencing an instance in the enclosing block
    if (1) begin : g_up
      function automatic logic [7:0] rdUp(input int a);
        return u_mid.rd(a);
      endfunction
    end
  end

  initial begin
    logic [7:0] o;
    `checkd(g_way[1].rdFunc(1), 17);
    `checkd(g_way[2].rdFunc(2), 34);
    `checkd(g_way[1].rdVar(3), 19);
    `checkd(g_way[2].rdVar(0), 32);
    g_way[2].rdTask(1, o);
    `checkd(o, 33);
    `checkd(g_way[2].rdSub(), 200);
    `checkd(g_way[1].rdGen(), 1);
    `checkd(g_way[2].rdIfc(), 2000);
    `checkd(g_way[1].rdSelf(2), 18);
    `checkd(g_way[2].rdAbs(3), 35);
    `checkd(g_way[2].rdBlock(1), 34);
    `checkd(g_way[2].rdBlock(1), 35);
    `checkd(g_way[1].rdBlock(1), 18);
    `checkd(g_way[1].g_inner.rdInner(0), 80);
    `checkd(g_way[2].g_inner.rdInner(1), 97);
    `checkd(g_way[2].g_up.rdUp(3), 35);
    g_way[1].wrVar(2, 99);
    `checkd(g_way[1].rdVar(2), 99);
    `checkd(g_way[2].rdVar(2), 34);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
