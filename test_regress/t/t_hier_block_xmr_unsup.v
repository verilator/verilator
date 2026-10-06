// DESCRIPTION: Verilator: Verilog Test module
//
// References out of a hierarchical block that cannot be promoted to a port.
// Each must be refused rather than silently mis-modelled, since a wrong width
// or a dropped write is wrong hardware.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module tech #(parameter W = 8) (input [W-1:0] phi, input real anal, input bit flag);
  parameter CONSTVAL = 3;
  function automatic bit getflag();
    return flag;
  endfunction
endmodule

// 1. Width is parameterized, so not knowable before elaboration
module leaf_param(output reg o, input i);
  wire [7:0] ph = t.top.drv.tech_inst.phi;
  always @(ph or i) o <= i ^ ph[0];
endmodule
module blk_param(output o, input i);
  /*verilator hier_block*/
  leaf_param l0(o, i);
endmodule

// 2. Non-integral type
module leaf_real(output reg o, input i);
  real r;
  always @(i) begin r = t.top.drv.tech_inst.anal; o <= i; end
endmodule
module blk_real(output o, input i);
  /*verilator hier_block*/
  leaf_real l0(o, i);
endmodule

// 3. Writing a signal outside the block
module leaf_write(output reg o, input i);
  always @(i) begin t.top.drv.tech_inst.flag = i; o <= i; end
endmodule
module blk_write(output o, input i);
  /*verilator hier_block*/
  leaf_write l0(o, i);
endmodule

// 4. Nested hierarchical block
module leaf_nest(output reg o, input i);
  always @(i) o <= i ^ t.top.drv.tech_inst.flag;
endmodule
module inner_nest(output o, input i);
  /*verilator hier_block*/
  leaf_nest l0(o, i);
endmodule
module blk_nest(output o, input i);
  /*verilator hier_block*/
  inner_nest n0(o, i);
endmodule

// 5. Generated port name collides with a signal the design already declares
module leaf_collide(output reg o, input i);
  reg xmrport_0;
  always @(i) begin xmrport_0 = t.top.drv.tech_inst.flag; o <= i ^ xmrport_0; end
endmodule
module blk_collide(output o, input i);
  /*verilator hier_block*/
  leaf_collide l0(o, i);
endmodule

// 6. Target is a parameter: a port would make a constant a runtime value
module leaf_const(output reg o, input i);
  always @(i) o <= i ^ t.top.drv.tech_inst.CONSTVAL[0];
endmodule
module blk_const(output o, input i);
  /*verilator hier_block*/
  leaf_const l0(o, i);
endmodule

// 7. Target is a function, which a port cannot carry
module leaf_call(output reg o, input i);
  always @(i) o <= i ^ t.top.drv.tech_inst.getflag();
endmodule
module blk_call(output o, input i);
  /*verilator hier_block*/
  leaf_call l0(o, i);
endmodule

// 8. Path indexes a scope, which the child run cannot spell back
module leaf_index(output reg o, input i);
  always @(i) o <= i ^ t.top.gen[1].g_tech.flag;
endmodule
module blk_index(output o, input i);
  /*verilator hier_block*/
  leaf_index l0(o, i);
endmodule

module drv(output reg [7:0] ph, output real anal, output bit flag);
  tech tech_inst(ph, anal, flag);
  initial begin ph = 8'h5a; anal = 1.0; flag = 1'b0; end
endmodule

module bench(output o, input i);
  wire [7:0] ph;
  real       anal;
  bit        flag;
  wire o1, o2, o3, o4, o5, o6, o7, o8;
  drv drv(ph, anal, flag);
  // An indexed scope for case 8 to reach into
  generate
    for (genvar gi = 0; gi < 2; ++gi) begin : gen
      tech g_tech(ph, anal, flag);
    end
  endgenerate
  blk_param p0(o1, i);
  blk_real  r0(o2, i);
  blk_write w0(o3, i);
  blk_nest  n0(o4, i);
  blk_collide c0(o5, i);
  blk_const  k0(o6, i);
  blk_call   f0(o7, i);
  blk_index  x0(o8, i);
  assign o = o1 ^ o2 ^ o3 ^ o4 ^ o5;
endmodule

module t;
  wire o;
  reg  i = 1'b1;
  bench top(o, i);
endmodule
