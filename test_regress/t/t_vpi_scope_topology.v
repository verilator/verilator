// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// VPI coverage of combinational shapes across non-trivial hierarchy: a comb net
// duplicated across instances, a submodule that drives an interface member owned by
// another scope, a cross-scope interface member read back through a different
// instance's port, an alias chain crossing a non-inlined instance boundary, a comb
// cycle closed through two instances, impure ($random/$time) and variable-index
// driven combinational logic, and a submodule output that is itself only a
// temporary feeding another output.

interface iface_t #(
    parameter W = 8
) (
    input logic [W-1:0] din
);
  logic [W-1:0] a;
  logic [W-1:0] b;
  assign a = din + 8'h11;
  assign b = a ^ 8'h5a;
endinterface

module sub_comb (
    input logic [7:0] din,
    output logic [7:0] dout
);
  /*verilator no_inline_module*/
  logic [7:0] s1;
  logic [7:0] s2;
  assign s1 = din + 8'h07;
  assign s2 = s1 + (din << 1);
  assign dout = s2;
endmodule

// An always_comb inside a submodule drives a member of an interface owned by a
// different scope.
interface swap_if #(
    parameter int DBW = 8
) ();
  logic [DBW-1:0][7:0] wdata;
  logic [DBW-1:0][7:0] swapped;

  function automatic logic [DBW-1:0][7:0] swap_endianness(logic [DBW-1:0][7:0] input_value);
    integer i;
    logic [DBW-1:0][7:0] input_value_swapped;
    for (i = 0; i < DBW; i++) input_value_swapped[DBW-1-i] = input_value[i];
    return input_value_swapped;
  endfunction

  modport slave(input wdata, output swapped, import swap_endianness);
endinterface

module sub_ifwrite (
    swap_if.slave s
);
  always_comb s.swapped = s.swap_endianness(s.wdata);
endmodule

// A comb driver in one instance feeds an interface member read by a different
// instance through its port.
interface xscope_if;
  logic v;
endinterface

module xscope_drv (
    input logic a,
    output logic v
);
  always_comb v = ~a;
endmodule

module xscope_rcv (
    xscope_if s,
    output logic o
);
  logic n;
  always_comb n = ~s.v;
  assign o = n;
endmodule

// A comb cycle closed through two inlined instances. The return leg ORs in a
// constant so the pair is neither optimised away nor left unsettled.
module combloop_pass (
    input logic [6:0] i,
    output logic [6:0] o
);
  assign o = i;
endmodule

// Not inlined, so the alias chain through u_chain crosses a real instance boundary.
module chain_pass8 (
    input logic [7:0] i,
    output logic [7:0] o
);
  /*verilator no_inline_module*/
  assign o = i;
endmodule

module t;

  logic clk;
  initial clk = 0;
  always #5 clk = ~clk;

  // Stimulus, one step per clock
  logic [7:0] base = 8'h0;
  logic [7:0] in0 = 8'h0;
  logic [7:0] in1 = 8'h0;
  logic [7:0] in2 = 8'h0;
  logic [7:0] in3 = 8'h0;
  logic [7:0][7:0] d = 64'h0;
  logic [2:0] idx = 3'h0;
  logic [3:0] nib = 4'h0;

  logic [7:0] cyc = 8'h0;
  always @(posedge clk) begin
    cyc <= cyc + 8'h1;
    case (cyc)
      8'd0: begin
        base <= 8'h01;
        {in0, in1, in2, in3} <= 32'h1122f055;
      end
      8'd1: begin
        base <= 8'h10;
        {in0, in1, in2, in3} <= 32'hdeadbeef;
      end
      8'd2: begin
        base <= 8'h7f;
        {in0, in1, in2, in3} <= 32'hff008001;
        d <= 64'h0011223344556677;
      end
      8'd3: begin
        base <= 8'h22;
        idx <= 3'h5;
        nib <= 4'ha;
      end
      8'd4: begin
        base <= 8'h00;
        nib <= 4'h0;
      end
      8'd5: begin
        base <= 8'h13;
        nib <= 4'h1;
      end
      8'd6: base <= 8'h40;
      8'd7: base <= 8'ha5;
      8'd8: base <= 8'hff;
      8'd9: base <= 8'h21;
      8'd10: base <= 8'h7e;
      8'd11: base <= 8'hc3;
      8'd13: begin
        t_vpi_dump_values();
        $write("*-* All Finished *-*\n");
        #1 $finish;
      end
      default: ;
    endcase
  end

  import "DPI-C" context function void t_vpi_dump_values();
  import "DPI-C" context function void t_vpi_dump_skip(input string name);

  // $random and $time are impure, as is obs, which reads them; and any values with
  // cyc_a ^ cyc_b == cyc_d close the comb cycle. None of these are dumped.
  initial begin
    t_vpi_dump_skip("t.rndc");
    t_vpi_dump_skip("t.tstamp");
    t_vpi_dump_skip("t.obs");
    t_vpi_dump_skip("t.cyc_a");
    t_vpi_dump_skip("t.cyc_b");
    t_vpi_dump_values();
  end
  always @(negedge clk) t_vpi_dump_values();

  logic [7:0][7:0] o;
  logic [7:0] obs;

  // A comb net duplicated across two interface instances and two submodule
  // instances must keep independent storage per instance.
  iface_t if0 (.din(base));
  iface_t if1 (.din(base + 8'h20));

  logic [7:0] out0;
  logic [7:0] out1;
  sub_comb u0 (
      .din(base),
      .dout(out0)
  );
  sub_comb u1 (
      .din(base + 8'h30),
      .dout(out1)
  );

  // Streaming operators per SV LRM: order-preserved, bit-reversed, byte-reversed,
  // and an array streamed the same way.
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
    logic [7:0] c;
  } stream_t;

  stream_t s;
  logic [7:0] arr[0:3];

  always_comb begin
    s.a = in0;
    s.b = in1;
    s.c = in2;
    arr[0] = in0;
    arr[1] = in1;
    arr[2] = in2;
    arr[3] = in3;
  end

  logic [23:0] flat_gg;  // {>>{s}}: order preserved
  logic [23:0] flat_ll;  // {<<{s}}: bit-reversed
  logic [23:0] flat_lb;  // {<<byte{s}}: byte-reversed
  logic [31:0] flat_arr_gg;  // {>>{arr}}: array streamed

  assign flat_gg = {>>{s}};
  assign flat_ll = {<<{s}};
  assign flat_lb = {<<byte{s}};
  assign flat_arr_gg = {>>{arr}};

  // Free-running comb cycle plus a rotated alias pair and a self-loop, all fed
  // from a free-running counter.
  logic [6:0] cyc_boundary = 7'h0;

  logic [6:0] cyc_d;
  assign cyc_d = cyc_boundary + 7'h1;

  // verilator lint_off UNOPTFLAT
  logic [6:0] cyc_a;
  logic [6:0] cyc_b;
  // verilator lint_on UNOPTFLAT
  assign cyc_a = cyc_b ^ cyc_d;
  assign cyc_b = cyc_a ^ cyc_d;

  logic [6:0] cyc_down;
  logic [6:0] cyc_down2;
  assign cyc_down = cyc_a ^ cyc_b;
  assign cyc_down2 = cyc_down + cyc_boundary;

  // verilator lint_off UNOPTFLAT
  logic [6:0] ali_a;
  logic [6:0] ali_b;
  // verilator lint_on UNOPTFLAT
  assign ali_a = ali_b;
  // Rotated on one side so the pair does not simplify to 'wire x = x'
  assign ali_b = {ali_a[5:0], ali_a[6]};

  // verilator lint_off UNOPTFLAT
  logic [6:0] self_loop;
  // verilator lint_on UNOPTFLAT
  assign self_loop = self_loop & cyc_boundary;

  always_ff @(posedge clk) cyc_boundary <= cyc_boundary + 7'h1;

  // A comb cycle closed through two instances, both inlined, with no external
  // input: it settles to a fixed point from a 2-state 0 start, and stays X from a
  // 4-state X start.
  // verilator lint_off UNOPTFLAT
  logic [6:0] alc_x;
  logic [6:0] alc_y;
  // verilator lint_on UNOPTFLAT
  combloop_pass u_pass1 (
      .i(alc_x),
      .o(alc_y)
  );
  combloop_pass u_pass2 (
      .i(alc_y | 7'h0a),
      .o(alc_x)
  );

  // sub_ifwrite drives intf.swapped from another scope entirely.
  swap_if intf ();
  assign intf.wdata = d;
  assign o = intf.swapped;
  sub_ifwrite u_ifwrite (intf);

  // An alias chain whose middle link crosses a non-inlined instance boundary
  // (chain_pass8's input pin); the reader downstream of the chain must stay
  // ordered after the deepest link's own logic.
  logic [7:0] chain_l0;
  logic [7:0] chain_l1;
  logic [7:0] chain_l2;
  logic [7:0] chain_l3;
  logic [7:0] chain_l4;
  logic [7:0] chain_deep;
  logic [7:0] chain_tap;
  logic [7:0] chain_use;
  assign chain_l0 = base + 8'h01;
  assign chain_l1 = chain_l0 + 8'h02;
  assign chain_l2 = chain_l1 + 8'h04;
  assign chain_l3 = chain_l2 + 8'h08;
  assign chain_l4 = chain_l3 + 8'h10;
  assign chain_deep = chain_l4 ^ 8'h3c;
  chain_pass8 u_chain (
      .i(chain_deep),
      .o(chain_tap)
  );
  assign chain_use = chain_tap ^ 8'ha5;

  // Variable-index write: only the selected 4-bit window is ever assigned.
  logic [7:0] crbase;
  always_comb crbase[idx+:4] = nib;

  // Unseeded $random is impure: re-executing it advances the model's shared RNG,
  // so its value is read but not compared.
  logic [7:0] rndc;
  always_comb rndc = 8'(nib) + 8'($random);

  // $time is impure, so its value is not dumped.
  logic [7:0] tstamp;
  always_comb tstamp = 8'(nib) + 8'($time);

  // u_portsrc's 'o' is a plain output port of a submodule, but internally it is
  // only a temporary feeding 'mix'; two different copy idioms read it.
  logic [31:0] pt_acc = 32'h0;
  logic [31:0] pt_o;
  logic [31:0] pt_obs;
  always_ff @(posedge clk) pt_acc <= pt_acc + {24'h0, base};

  portsrc u_portsrc (
      .i(pt_acc),
      .o(pt_o),
      .obs(pt_obs)
  );

  xscope_if xscope_bus ();
  logic xscope_o;
  xscope_drv u_xscope_drv (
      .a(nib[0]),
      .v(xscope_bus.v)
  );
  xscope_rcv u_xscope_rcv (
      .s(xscope_bus),
      .o(xscope_o)
  );

  assign obs = out0 ^ out1 ^ flat_gg[7:0] ^ {1'b0, cyc_down2} ^ o[0] ^ crbase ^ rndc
             ^ tstamp ^ {1'b0, alc_x} ^ chain_use ^ pt_obs[7:0] ^ {7'h0, xscope_o};

endmodule

// A submodule output that is only a temporary feeding another output.
module portsrc (
    input logic [31:0] i,
    output logic [31:0] o,
    output logic [31:0] obs
);
  /* verilator no_inline_module */

  logic [31:0] mix;
  logic [31:0] cpy_a;
  logic [31:0] cpy_c;

  // 'o' is a temporary that only feeds 'mix'.
  always_comb begin
    o = i ^ 32'h5a5a_0000;
    mix = o + 32'd3;
  end

  // Both copy idioms must read the same temporary value.
  always_comb cpy_a = o;
  assign cpy_c = o;

  assign obs = (mix ^ cpy_a) + cpy_c;

endmodule
