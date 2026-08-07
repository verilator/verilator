// DESCRIPTION: Verilator: Verilog Test module
//
// Struct localparam field access via a class-scope Dot used in a cell
// parameter pin (e.g. `CFG::cfg.jt.cam_type`), where CFG is a typedef
// alias of a parameterized class.  V3LinkDot defers the `CFG::cfg` Dot
// until post-V3Param; when the cell is deparameterized, resolveDotToTypedef
// folds the class localparam to a Const and must then walk up the outer
// `.field[.field...]` Dot chain, accumulating the packed-struct bit offset,
// and replace the topmost Dot with a Sel(const, lsb, width) matching
// V3Width::memberSelStruct.  Without this, the struct-field select on the
// deferred class localparam cannot be constified for the cell pin.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct packed {
  logic [7:0] cam_type;
  logic [7:0] depth;
} inner_t;

typedef struct packed {
  inner_t     jt;
  logic [7:0] tag;
} cfg_t;

class C #(parameter int W = 1);
  // Struct localparam whose fields derive from the class parameter.
  localparam cfg_t cfg = '{jt: '{cam_type: W[7:0], depth: W[7:0] + 8'd1},
                           tag: W[7:0] + 8'd2};
endclass

// Wrapper class containing the use of another class
class D #(parameter int W = 1);
  typedef C#(W) CC;
  localparam int q = int'(CC::cfg.tag) + 100;
endclass

module Sub #(parameter int WIDTH = 0) ();
endmodule

// Parameterized wrapper so the class specialization is deferred until
// V3Param processes the cell instance.
module Mid #(parameter int W = 8) ();
  typedef C#(W) CFG;
  // (1) single-level struct field access -> one loop iteration
  Sub #(int'(CFG::cfg.tag)) u_tag ();
  // (2) nested struct field access -> two loop iterations, lsb accumulation
  Sub #(int'(CFG::cfg.jt.cam_type)) u_cam ();
  Sub #(int'(CFG::cfg.jt.depth)) u_depth ();
  // (3) nested struct-field Dot buried in a wrapper class's lparam value
  typedef D#(W) DD;
  Sub #(int'(DD::q)) u_q ();
endmodule

module t;
  Mid #(.W(8)) u ();

  initial begin
    // cfg.tag = W + 2 = 10 (offset above the 16-bit jt struct)
    `checkh(u.u_tag.WIDTH, 32'd10);
    // cfg.jt.cam_type = W = 8 (nested, lsb 0)
    `checkh(u.u_cam.WIDTH, 32'd8);
    // cfg.jt.depth = W + 1 = 9 (nested, lsb 8)
    `checkh(u.u_depth.WIDTH, 32'd9);
    // q = cfg.tag + 100 = 10 + 100 = 110
    `checkh(u.u_q.WIDTH, 32'd110);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
