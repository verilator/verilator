// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Functions whose only side effect is writing an output, inout or ref
// argument: a call that the short-circuit operators (IEEE 1800-2023 11.3.5)
// skip must not write the argument, and a call that is evaluated must write
// it even when its result is not needed.

package pkg;
  function automatic bit pkg_out(input int s, output int v);
    v = 0;
    if (s < 0) return 1'b0;
    v = s;
    return 1'b1;
  endfunction
endpackage

class Cls;
  int m;
  function bit meth_out(input int s, output int v);
    v = 0;
    if (s < 0) return 1'b0;
    v = s;
    return 1'b1;
  endfunction
  function void check(bit x, int s);
    m = 77;
    if (x && meth_out(s, m)) m = m + 1000;
    `checkd(m, !x ? 77 : s < 0 ? 0 : s + 1000);
    m = 77;
    if (x && pkg::pkg_out(s, m)) m = m + 1000;
    `checkd(m, !x ? 77 : s < 0 ? 0 : s + 1000);
  endfunction
endclass

module t (
    input clk
);
  int cyc = 0;

  // Writes 0 to v, returns 0 if s is negative, else writes s and returns 1
  function automatic bit f_out(input int s, output int v);
    v = 0;
    if (s < 0) return 1'b0;
    v = s;
    return 1'b1;
  endfunction
  function automatic bit f_inout(input int s, inout int v);
    if (s < 0) return 1'b0;
    v = v + s;
    return 1'b1;
  endfunction
  function automatic int f_outi(input int s, output int v);
    v = 0;
    if (s < 0) return s;
    v = s;
    return s;
  endfunction
  function automatic bit f_outd(input int s = 7, output int v);
    v = s;
    return 1'b1;
  endfunction
  function automatic bit f_ref(input int s, ref int v);
    if (s < 0) return 1'b0;
    v = v + s;
    return 1'b1;
  endfunction

  bit x;  // Varies 0, 1
  int s;  // Varies -1, 0, 1, ...
  int a, b;
  int arr[3];
  bit r;
  Cls cls = new;

  // Combinational use
  int comb_v;
  always_comb begin
    comb_v = 55;
    if (x && f_out(s, comb_v)) comb_v = comb_v + 1000;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    // Settled from the previous cycle's x and s
    `checkd(comb_v, !x ? 55 : s < 0 ? 0 : s + 1000);
    x = cyc[0];
    s = cyc / 2 - 1;

    // && in if condition, output argument
    a = 11;
    if (x && f_out(s, a)) a = a + 1000;
    `checkd(a, !x ? 11 : s < 0 ? 0 : s + 1000);
    // In else-if
    a = 11;
    if (cyc < 0) a = 99;
    else if (x && f_out(s, a)) a = a + 1000;
    `checkd(a, !x ? 11 : s < 0 ? 0 : s + 1000);
    // ||
    a = 11;
    if (!x || f_out(s, a)) a = a + 1000;
    `checkd(a, !x ? 1011 : s < 0 ? 0 : s + 1000);
    // ?: then and else operands
    a = 11;
    b = 22;
    r = x ? f_out(s, a) : f_out(s + 1, b);
    `checkd(a, !x ? 11 : s < 0 ? 0 : s);
    `checkd(b, x ? 22 : s + 1 < 0 ? 0 : s + 1);
    // Implication
    a = 11;
    if (x -> f_out(s, a)) a = a + 1000;
    `checkd(a, !x ? 1011 : s < 0 ? 0 : s + 1000);
    // Chained calls: second skipped when the first returns 0
    a = 11;
    b = 22;
    r = f_out(s, a) && f_out(s + 5, b);
    `checkd(a, s < 0 ? 0 : s);
    `checkd(b, s < 0 ? 22 : s + 5);
    // Evaluated call with nothing depending on the result still writes
    a = 11;
    b = 22;
    if (f_out(s, a) && f_out(s + 5, b)) begin
    end
    `checkd(a, s < 0 ? 0 : s);
    `checkd(b, s < 0 ? 22 : s + 5);
    // Plain assignment and expression context
    a = 11;
    r = x && f_out(s, a);
    `checkd(a, !x ? 11 : s < 0 ? 0 : s);
    a = 11;
    r = !(x && f_out(s, a)) ^ x;
    `checkd(a, !x ? 11 : s < 0 ? 0 : s);
    // Array element as the output argument
    arr[1] = 11;
    if (x && f_out(s, arr[1])) arr[1] = arr[1] + 1000;
    `checkd(arr[1], !x ? 11 : s < 0 ? 0 : s + 1000);
    // Inout and ref arguments
    a = 11;
    if (x && f_inout(s, a)) a = a + 1000;
    `checkd(a, !x ? 11 : s < 0 ? 11 : 11 + s + 1000);
    a = 11;
    if (x && f_ref(s, a)) a = a + 1000;
    `checkd(a, !x ? 11 : s < 0 ? 11 : 11 + s + 1000);
    // Package function and class method
    a = 11;
    if (x && pkg::pkg_out(s, a)) a = a + 1000;
    `checkd(a, !x ? 11 : s < 0 ? 0 : s + 1000);
    cls.check(x, s);
    // Constant other operand: the call is still the evaluated operand
    a = 11;
    r = f_out(s, a) && 1'b0;
    `checkd(a, s < 0 ? 0 : s);
    `checkd(r, 1'b0);
    a = 11;
    r = f_out(s, a) || 1'b1;
    `checkd(a, s < 0 ? 0 : s);
    `checkd(r, 1'b1);
    // Case item condition
    a = 11;
    case (1'b1)
      (x && f_out(s, a)): a = a + 1000;
      default: ;
    endcase
    `checkd(a, !x ? 11 : s < 0 ? 0 : s + 1000);
    // Call inside the argument list of a skipped call
    a = 11;
    b = 22;
    r = x && f_out(f_outi(s, b), a);
    `checkd(a, !x ? 11 : s < 0 ? 0 : s);
    `checkd(b, !x ? 22 : s < 0 ? 0 : s);
    // Omitted argument taking its default
    a = 11;
    r = x && f_outd(, a);
    `checkd(a, !x ? 11 : 7);
    // Operand beside an all-ones '|', or under an out-of-range shift
    a = 11;
    r = 1'b1 | f_out(s, a);
    `checkd(a, s < 0 ? 0 : s);
    a = 11;
    r = f_out(s, a) | 1'b1;
    `checkd(a, s < 0 ? 0 : s);
    a = 11;
    b = int'(f_out(s, a)) << 40;
    `checkd(a, s < 0 ? 0 : s);
    a = 11;
    b = int'(f_out(s, a)) >> 40;
    `checkd(a, s < 0 ? 0 : s);
    // Condition of a conditional whose two arms are identical
    a = 11;
    r = f_out(s, a) ? 1 : 1;
    `checkd(a, s < 0 ? 0 : s);
    // Result assigned to a temporary that is never read
    a = 11;
    if (f_out(s, a)) begin
    end else begin
    end
    `checkd(a, s < 0 ? 0 : s);

    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
