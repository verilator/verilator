// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  bit [1:0] a;
  bit [1:0] b;
  real r;
  typedef struct packed {logic [1:0] f;} cfg_t;
  cfg_t cfg;

  covergroup cg(ref int bound) with function sample (bit [1:0] s);
    aa: coverpoint a;
    bb: coverpoint b;
    rr: coverpoint r {bins low = {[0.0 : 1.0]};}
    xx: cross aa, bb{
      bins wrong_cross = missing with (aa == bb);  // <--- Bad: not the enclosing cross
      bins sampled = xx with (aa == s);  // <--- Bad: a sample argument
      bins referenced = xx with (int'(aa) < bound);  // <--- Bad: a ref constructor argument
    }
    xr: cross aa, rr{
      bins real_value = (xr with (rr < 0.5 || rr > 0.9)) || xr;  // <--- Unsupported: real value
      bins real_unread = xr with (aa == 1);
    }
    xd: cross aa, aa{
      bins high = xd with (aa > 1);  // One candidate of a repeated item
    }
    xh: cross aa, cfg.f{  // <--- Unsupported: hierarchical item
      bins any = xh with (aa == 1);
    }
  endgroup

  int limit;
  cg inst = new(limit);
endmodule
