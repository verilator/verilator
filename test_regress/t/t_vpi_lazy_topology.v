// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Topology-driven reconstruct/retain: each block hinges on a distinct top-level shape that
// cannot be expressed as extra signals on one flat module.

// multi: shared classes dedup shadow storage per instance
interface iface_t #(parameter W = 8) (input logic [W-1:0] din);
  logic [W-1:0] a;
  logic [W-1:0] b;
  assign a = din + 8'h11;
  assign b = a ^ 8'h5a;
endinterface

module sub_multi (input logic clk, input logic [7:0] din, output logic [7:0] dout);
  /*verilator no_inline_module*/
  logic [7:0] s1;
  logic [7:0] s2;
  assign s1 = din + 8'h07;
  assign s2 = s1 + (din << 1);
  assign dout = s2;
  logic [7:0] wo;
  always_ff @(posedge clk) wo <= din + 8'h11;
endmodule

// creset: always_comb in sub_creset drives an interface member owned by another scope, so
// the group is retained.
interface swap_if #(
  parameter int DBW = 8
) ();
  logic [DBW-1:0][7:0] wdata;
  logic [DBW-1:0][7:0] swapped;

  function automatic logic [DBW-1:0][7:0] swap_endianness(logic [DBW-1:0][7:0] input_value);
    integer i;
    logic [DBW-1:0][7:0] input_value_swapped;
    for (i = 0; i < DBW; i++) input_value_swapped[DBW - 1 - i] = input_value[i];
    return input_value_swapped;
  endfunction

  modport slave(input wdata, output swapped, import swap_endianness);
endinterface

module sub_creset (swap_if.slave s);
  always_comb s.swapped = s.swap_endianness(s.wdata);
endmodule

module t (
  input  logic        clk,
  input  logic [7:0]  base,
  input  logic [7:0]  in0,
  input  logic [7:0]  in1,
  input  logic [7:0]  in2,
  input  logic [7:0]  in3,
  input  logic [7:0][7:0] d,
  output logic [7:0][7:0] o,
  input  logic [2:0]  idx,
  input  logic [3:0]  nib,
  output logic [7:0]  obs
);

  // multi
  iface_t #(.W(8)) if0 (.din(base));
  iface_t #(.W(8)) if1 (.din(base + 8'h20));

  logic [7:0] out0;
  logic [7:0] out1;
  sub_multi u0 (.clk(clk), .din(base),         .dout(out0));
  sub_multi u1 (.clk(clk), .din(base + 8'h30), .dout(out1));

  logic [7:0] acc;
  always_ff @(posedge clk) begin
    acc <= acc + if0.b + if1.b + out0 + out1;
  end

  // stream: reconstructed for VPI
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
    logic [7:0] c;
  } us_t;

  us_t        s;
  logic [7:0] arr [0:3];

  always_ff @(posedge clk) begin
    s.a    <= in0;
    s.b    <= in1;
    s.c    <= in2;
    arr[0] <= in0;
    arr[1] <= in1;
    arr[2] <= in2;
    arr[3] <= in3;
  end

  logic [23:0] flat_gg;     // {>>{s}}: order preserved
  logic [23:0] flat_ll;     // {<<{s}}: bit-reversed
  logic [23:0] flat_lb;     // {<<byte{s}}: byte-reversed
  logic [31:0] flat_arr_gg; // {>>{arr}}: array streamed

  assign flat_gg     = {>>{s}};
  assign flat_ll     = {<<{s}};
  assign flat_lb     = {<<byte{s}};
  assign flat_arr_gg = {>>{arr}};

  // cycle: comb cycles retained; the alias cycle below is separate
  logic [6:0] cyc_boundary;

  logic [6:0] cyc_d;  // reconstructed, feeds cycle
  assign cyc_d = cyc_boundary + 7'h1;

  logic [6:0] cyc_a;
  logic [6:0] cyc_b;
  assign cyc_a = cyc_b ^ cyc_d;
  assign cyc_b = cyc_a ^ cyc_d;

  logic [6:0] cyc_down;
  logic [6:0] cyc_down2;
  assign cyc_down  = cyc_a ^ cyc_b;
  assign cyc_down2 = cyc_down + cyc_boundary;

  logic [6:0] ali_a;
  logic [6:0] ali_b;
  assign ali_a = ali_b;
  // Rotated on one side so the pair does not const-fold to 'wire x = x'
  assign ali_b = {ali_a[5:0], ali_a[6]};

  logic [6:0] self_loop;
  assign self_loop = self_loop & cyc_boundary;

  always_ff @(posedge clk) cyc_boundary <= cyc_boundary + 7'h1;

  // aliascycle: each side is a whole-net alias of the other, so Bail::ALIAS_CYCLE rather
  // than a comb cycle
  logic [6:0] alc_x;
  logic [6:0] alc_y;
  t_vpi_lazy_topology_pass u_pass1 (.i(alc_x), .o(alc_y));
  t_vpi_lazy_topology_pass u_pass2 (.i(alc_y), .o(alc_x));

  // creset
  swap_if #(.DBW(8)) intf ();
  assign intf.wdata = d;
  assign o = intf.swapped;
  sub_creset u_creset (intf);

  // chainorder: the input pin of a non-inlined instance is a cross-scope write, so that link
  // of the alias chain is retained. co_tap's chain still resolves past it to co_deep, and the
  // reader that retarget moves onto co_deep must stay ordered after co_deep's cone.
  logic [7:0] co_l0;
  logic [7:0] co_l1;
  logic [7:0] co_l2;
  logic [7:0] co_l3;
  logic [7:0] co_l4;
  logic [7:0] co_deep;
  logic [7:0] co_tap;
  logic [7:0] co_use;
  assign co_l0 = base + 8'h01;
  assign co_l1 = co_l0 + 8'h02;
  assign co_l2 = co_l1 + 8'h04;
  assign co_l3 = co_l2 + 8'h08;
  assign co_l4 = co_l3 + 8'h10;
  assign co_deep = co_l4 ^ 8'h3c;
  t_vpi_lazy_topology_pass8 u_chain (.i(co_deep), .o(co_tap));
  assign co_use = co_tap ^ 8'ha5;

  // contretain: impure and variable-index drivers must be retained
  logic [31:0] seed;
  logic [31:0] rnd;
  assign rnd = $urandom(seed);

  logic [7:0] crbase;
  assign crbase[idx +: 4] = nib;

  // Unseeded $random is pure, but re-executing it would advance the model's shared RNG
  logic [7:0] rndc;
  always_comb rndc = 8'(nib) + 8'($random);

  // $time reads simulation state no variable captures
  logic [7:0] tstamp;
  always_comb tstamp = 8'(nib) + 8'($time);

  assign obs = acc[7:0] ^ flat_gg[7:0] ^ {1'b0, cyc_down2} ^ o[0] ^ crbase ^ rndc ^ tstamp
             ^ rnd[7:0] ^ {1'b0, alc_x} ^ co_use;

endmodule

module t_vpi_lazy_topology_pass8 (
  input  logic [7:0] i,
  output logic [7:0] o
);
  /*verilator no_inline_module*/
  assign o = i;
endmodule

module t_vpi_lazy_topology_pass (
  input  logic [6:0] i,
  output logic [6:0] o
);
  assign o = i;
endmodule
