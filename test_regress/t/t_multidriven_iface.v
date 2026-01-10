// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// Consolidated interface-based multidriven tests
// (formerly t_multidriven_iface{0,1,2,3,4,5,6}.v)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

//----------------------------------------------------------------------
// iface0: direct assignment to interface signal + interface task assign in same process

interface my_if0;
  logic l0;
  task set_l0_1();
    l0 = 1'b1;
  endtask
  task set_l0_0();
    l0 = 1'b0;
  endtask
endinterface

module iface0 #(
) (
    input logic sel,
    output logic val
);
  my_if0 if0 ();
  always_comb begin
    if0.l0 = 1'b0;
    if (sel) begin
      if0.set_l0_1();
    end
  end
  assign val = if0.l0;
endmodule

//----------------------------------------------------------------------
// iface1: interface task chain - nested calls write interface signal in same always_comb

interface my_if1;
  logic l0;
  task set_l0_1_inner();
    l0 = 1'b1;
  endtask
  task set_l0_1_outer();
    set_l0_1_inner();
  endtask
endinterface

module iface1 #(
) (
    input logic sel,
    output logic val
);
  my_if1 if0 ();
  always_comb begin
    if0.l0 = 1'b0;
    if (sel) begin
      if0.set_l0_1_outer();
    end
  end
  assign val = if0.l0;
endmodule

//----------------------------------------------------------------------
// iface2: interface passed through module port - direct assign + task call in same always_comb

interface my_if2;
  logic l0;
  task set_l0_1();
    l0 = 1'b1;
  endtask
  task set_l0_0();
    l0 = 1'b0;
  endtask
endinterface

module iface2 #(
) (
    input logic sel,
    output logic val,
    my_if2 ifp
);
  always_comb begin
    ifp.l0 = 1'b0;
    if (sel) begin
      ifp.set_l0_1();
    end
  end
  assign val = ifp.l0;
endmodule

//----------------------------------------------------------------------
// iface3: interface modport + task import - write interface signal in same always_comb

interface my_if3;
  logic l0;
  task set_l0_1();
    l0 = 1'b1;
  endtask
  modport mp(output l0, import set_l0_1);
endinterface

module iface3 #(
) (
    input logic sel,
    output logic val,
    my_if3.mp ifp
);
  always_comb begin
    ifp.l0 = 1'b0;
    if (sel) begin
      ifp.set_l0_1();
    end
  end
  assign val = ifp.l0;
endmodule

//----------------------------------------------------------------------
// iface4: interface task writes through output formal - actual is interface member

interface my_if4;
  logic l0;
  task automatic set_any(output logic q);
    q = 1'b1;
  endtask
endinterface

module iface4 #(
) (
    input logic sel,
    output logic val
);
  my_if4 if0 ();
  always_comb begin
    if0.l0 = 1'b0;
    if (sel) begin
      if0.set_any(if0.l0);
    end
  end
  assign val = if0.l0;
endmodule

//----------------------------------------------------------------------
// iface5: nested interface test - direct assignment + nested interface task call in same always_comb

interface leaf_if5;
  logic l0;
  task set1();
    l0 = 1'b1;
  endtask
endinterface

interface top_if5;
  leaf_if5 sub ();
endinterface

module iface5 #(
) (
    input logic sel,
    output logic val
);
  top_if5 if0 ();
  always_comb begin
    if0.sub.l0 = 1'b0;
    if (sel) begin
      if0.sub.set1();
    end
  end
  assign val = if0.sub.l0;
endmodule

//----------------------------------------------------------------------
// iface6: nested interface aggregator - two nested interfaces, only one driven

interface chan_if6;
  logic b0;
  task set1();
    b0 = 1'b1;
  endtask
endinterface

interface agg_if6;
  chan_if6 tlb ();
  chan_if6 ic ();
endinterface

module iface6 #(
) (
    input logic sel,
    output logic val
);
  agg_if6 a ();
  always_comb begin
    a.tlb.b0 = 1'b0;
    if (sel) a.tlb.set1();
  end
  assign val = a.tlb.b0;
endmodule

//----------------------------------------------------------------------
// Shared TB

module m_tb #() ();

  logic sel;
  logic val0, val1, val2, val3, val4, val5, val6;

  my_if2 if2 ();
  my_if3 if3 ();

  iface0 u0 (
      .sel(sel),
      .val(val0)
  );
  iface1 u1 (
      .sel(sel),
      .val(val1)
  );
  iface2 u2 (
      .sel(sel),
      .val(val2),
      .ifp(if2)
  );
  iface3 u3 (
      .sel(sel),
      .val(val3),
      .ifp(if3)
  );
  iface4 u4 (
      .sel(sel),
      .val(val4)
  );
  iface5 u5 (
      .sel(sel),
      .val(val5)
  );
  iface6 u6 (
      .sel(sel),
      .val(val6)
  );

  task automatic check_all(input logic exp);
    `checkd(val0, exp);
    `checkd(val1, exp);
    `checkd(val2, exp);
    `checkd(val3, exp);
    `checkd(val4, exp);
    `checkd(val5, exp);
    `checkd(val6, exp);
  endtask

  initial begin
    #1;
    sel = 'b0;
    #1;
    check_all(1'b0);

    sel = 'b1;
    #1;
    check_all(1'b1);

    sel = 'b0;
    #1;
    check_all(1'b0);
  end

  initial begin
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
