// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// Constant functions building, reading and returning unpacked structures, and arrays of them

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Issue #4285, as t_struct_param but unpacked
package config_pkg;
  typedef struct {
    int UPPER0;
    struct {
      int USE_QUAD0;
      int USE_QUAD1;
      int USE_QUAD2;
    } mac;
    int UPPER2;
  } config_struct_t;

  function automatic config_struct_t static_config(int selector);
    config_struct_t return_config;
    return_config = '{default: 0};
    return_config.UPPER0 = 10;
    return_config.UPPER2 = 20;
    return_config.mac.USE_QUAD0 = 4;
    return_config.mac.USE_QUAD2 = 6;
    case (selector)
      1: return_config.mac.USE_QUAD1 = 5;
    endcase
    return return_config;
  endfunction
endpackage

module struct_submodule
  import config_pkg::*;
#(
    parameter config_struct_t MY_CONFIG = '{default: 0}
);
  initial begin
    `checkd(MY_CONFIG.UPPER0, 10);
    `checkd(MY_CONFIG.mac.USE_QUAD0, 4);
    `checkd(MY_CONFIG.mac.USE_QUAD1, 5);
    `checkd(MY_CONFIG.mac.USE_QUAD2, 6);
    `checkd(MY_CONFIG.UPPER2, 20);
  end
endmodule

typedef struct {
  bit en;
  int w;
} cfg_t;

typedef struct {
  logic [6:0] l;
  real r;
  string s;
  cfg_t c;
} mix_t;

typedef cfg_t cfgs_t[3:1];

function automatic cfg_t new_cfg(int w);
  return '{en: w > 10, w: w};
endfunction

function automatic int get_w(cfg_t c);
  return c.w;
endfunction

// Given a structure, from a function of the parent
module leaf #(
    parameter cfg_t C = '{1'b0, 0},
    parameter int EXP_W = 0
) ();
  logic [C.w-1:0] q;
  localparam int W = get_w(C);
  initial begin
    `checkd($bits(q), EXP_W);
    `checkd(W, EXP_W);
  end
endmodule

// Reading members of an array of structures in a loop (corundum)
module core #(
    parameter int N = 2,
    parameter cfg_t IF_CFG[N] = '{'{1'b1, 8}, '{1'b1, 8}},
    parameter int EXP_MAX_W = 8,
    parameter int EXP_EN = 2
) ();
  function automatic int max_w();
    max_w = 0;
    for (int n = 0; n < N; ++n) if (IF_CFG[n].w > max_w) max_w = IF_CFG[n].w;
  endfunction
  function automatic int count_en(cfg_t cfgs[N]);
    count_en = 0;
    foreach (cfgs[n]) count_en += int'(cfgs[n].en);
  endfunction
  localparam int MAX_W = max_w();
  localparam int EN = count_en(IF_CFG);
  initial begin
    `checkd(MAX_W, EXP_MAX_W);
    `checkd(EN, EXP_EN);
  end
endmodule

module t;
  // Return of a pattern
  function automatic cfg_t f_pattern(int x);
    return '{x[0], x + 1};
  endfunction
  // Members of the return variable
  function automatic cfg_t f_members(int x);
    f_members.en = 1'b1;
    f_members.w = x * 2;
  endfunction
  // A local copied, edited and returned, keeping the copy's source
  localparam cfg_t P = '{1'b1, 33};
  function automatic cfg_t f_copy(int x);
    cfg_t r;
    r = P;
    r.w = r.w + x;
    if (P.w != 33) r.w = 0;
    return r;
  endfunction
  // A choice of constant patterns
  function automatic cfg_t f_choice(bit sel);
    if (sel) return '{1'b1, 2};
    else return '{1'b0, 4};
  endfunction
  // Members of other types, and a nested structure
  function automatic mix_t f_mix(int x);
    mix_t m;
    m.l = x[6:0];
    m.r = 1.5 * real'(x);
    m.s = (x > 2) ? "big" : "small";
    m.c = new_cfg(x);
    m.c.w = m.c.w + 1;
    return m;
  endfunction
  // An array of structures, built element by element
  function automatic cfgs_t f_array();
    for (int i = 1; i <= 3; ++i) begin
      f_array[i].en = i[0];
      f_array[i].w = 10 * i;
    end
    f_array[2] = f_array[1];
  endfunction
  // A structure built in a loop, through a select of a member
  function automatic int f_loop(int n);
    cfg_t c;
    c = '{1'b0, 0};
    for (int i = 0; i < n; ++i) c.w += i;
    return c.w;
  endfunction
  // Comparisons of whole structures and arrays of them
  function automatic int f_compare(cfg_t a, cfg_t b);
    cfgs_t x;
    cfgs_t y;
    mix_t m;
    mix_t n;
    x = '{default: a};
    y = x;
    y[2] = b;
    m = f_mix(1);
    n = f_mix(1);
    n.c.w = 9;
    return int'({27'(0), m == n, a == b, a != b, a === a, x == y});
  endfunction
  // Recursion with a structure argument
  function automatic int f_recurse(cfg_t c);
    cfg_t d;
    if (c.w == 0) return 0;
    d = c;
    d.w = c.w - 1;
    return c.w + f_recurse(d);
  endfunction
  // Issue #3826: an array of structures built in a loop over its size, used by a generate
  typedef cfg_t list_t[3];
  function list_t make_list;
    for (int j = 0; j < $size(make_list); ++j) begin
      make_list[j].en = j[0];
      make_list[j].w = 10 * j + 1;
    end
  endfunction
  localparam list_t LIST = make_list();
  for (genvar j = 0; j < $size(LIST); ++j) begin : g_list
    logic [LIST[j].w-1:0] q;
    initial begin
      `checkd($bits(q), 10 * j + 1);
      `checkd(LIST[j].en, 1'(j % 2));
    end
  end

  localparam config_pkg::config_struct_t MY_CONFIG = config_pkg::static_config(1);
  struct_submodule #(.MY_CONFIG(MY_CONFIG)) a_submodule_I ();

  localparam cfg_t PATTERN = f_pattern(3);
  localparam cfg_t MEMBERS = f_members(3);
  localparam cfg_t COPY = f_copy(4);
  localparam cfg_t CHOICE1 = f_choice(1'b1);
  localparam cfg_t CHOICE0 = f_choice(1'b0);
  localparam mix_t MIX = f_mix(5);
  localparam cfgs_t ARRAY = f_array();
  localparam int MEMBER_W = f_pattern(9).w;
  localparam int GET_W = get_w(P);
  localparam int LOOP = f_loop(5);
  localparam int RECURSE = f_recurse('{1'b1, 4});
  localparam int COMPARE_EQ = f_compare('{1'b1, 5}, '{1'b1, 5});
  localparam int COMPARE_NE = f_compare('{1'b1, 5}, '{1'b1, 6});

  leaf #(
      .C(new_cfg(13)),
      .EXP_W(13)
  ) u_leaf ();
  leaf #(
      .C(f_members(3)),
      .EXP_W(6)
  ) u_leaf_members ();

  core u_core_default ();
  core #(
      .IF_CFG('{'{1'b1, 16}, '{1'b0, 64}}),
      .EXP_MAX_W(64),
      .EXP_EN(1)
  ) u_core ();

  initial begin
    `checkd(PATTERN.en, 1'b1);
    `checkd(PATTERN.w, 4);
    `checkd(MEMBERS.en, 1'b1);
    `checkd(MEMBERS.w, 6);
    `checkd(COPY.w, 37);
    `checkd(P.w, 33);
    `checkd(CHOICE1.w, 2);
    `checkd(CHOICE0.en, 1'b0);
    `checkd(CHOICE0.w, 4);
    `checkd(MIX.l, 7'd5);
    `checkr(MIX.r, 7.5);
    `checks(MIX.s, "big");
    `checkd(MIX.c.en, 1'b0);
    `checkd(MIX.c.w, 6);
    `checkd(ARRAY[1].en, 1'b1);
    `checkd(ARRAY[1].w, 10);
    `checkd(ARRAY[2].en, 1'b1);
    `checkd(ARRAY[2].w, 10);
    `checkd(ARRAY[3].w, 30);
    `checkd(MEMBER_W, 10);
    `checkd(GET_W, 33);
    `checkd(LOOP, 10);
    `checkd(RECURSE, 10);
    `checkd(COMPARE_EQ, 'b0_1011);
    `checkd(COMPARE_NE, 'b0_0110);
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
