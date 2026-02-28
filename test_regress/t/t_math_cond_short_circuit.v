// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`ifdef verilator
 `define optimize_barrier $c("")
`else
 `define optimize_barrier
`endif
// verilog_format: on

module t;

  class Map;
    virtual function bit [95:0] get_value();
      bit [95:0] result = 96'h11111111_22222222_33333333;
      `optimize_barrier;
      return result;
    endfunction
  endclass

  class Cls;
    function bit [95:0] get_default();
      bit [95:0] result = 96'haaaaaaaa_bbbbbbbb_cccccccc;
      `optimize_barrier;
      return result;
    endfunction

    function bit [95:0] compute_LL(Map map);
      bit [95:0] result;
      `optimize_barrier;
      // Wide operation is required, as results in VL_COND call which evaluates
      // arguments
      result = map == null ? this.get_default() : map.get_value();
      `optimize_barrier;
      return result;
    endfunction

    function bit [95:0] compute_LC(Map map);
      bit [95:0] result;
      bit sel1 = map == null;
      `optimize_barrier;
      result = sel1 ? 96'hffffffff_ffffffff_ffffffff : map.get_value();
      `optimize_barrier;
      return result;
    endfunction

    function bit [95:0] compute_CL(Map map);
      bit [95:0] result;
      bit sel1 = map != null;
      `optimize_barrier;
      result = sel1 ? map.get_value() : 96'hffffffff_ffffffff_ffffffff;
      `optimize_barrier;
      return result;
    endfunction

  endclass

  initial begin
    Cls c;
    Map mnull;
    Map m;
    bit [95:0] res;

    c = new;
    m = new;

    res = c.compute_LL(mnull);
    `checkh(res, 96'haaaaaaaa_bbbbbbbb_cccccccc);
    res = c.compute_LL(m);
    `checkh(res, 96'h11111111_22222222_33333333);

    res = c.compute_LC(mnull);
    `checkh(res, 96'hffffffff_ffffffff_ffffffff);
    res = c.compute_LC(m);
    `checkh(res, 96'h11111111_22222222_33333333);

    res = c.compute_CL(mnull);
    `checkh(res, 96'hffffffff_ffffffff_ffffffff);
    res = c.compute_CL(m);
    `checkh(res, 96'h11111111_22222222_33333333);

    $finish;
  end

endmodule
