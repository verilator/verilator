// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc, bump, result;
  logic foo;
  initial begin
    cyc = 0;
    foo = '1;
  end


  always @(posedge clk) begin
    if (($time != 0) && foo) bump <= bump + 1;
    if (($realtime != 0) && foo) bump <= bump + 1;
    if (($stime != 0) && foo) bump <= bump + 1;
    if (($bitstoreal(123) != 0) && foo) bump <= bump + 1;
    if (($itor(123) != 0) && foo) bump <= bump + 1;
    if (($signed(3) != 0) && foo) bump <= bump + 1;
    if (($realtobits(1.23) != 0) && foo) bump <= bump + 1;
    if (($rtoi(1.23) != 0) && foo) bump <= bump + 1;
    if (($unsigned(-3) != 0) && foo) bump <= bump + 1;
    if (($clog2(123) != 0) && foo) bump <= bump + 1;
    if (($ln(123) != 0) && foo) bump <= bump + 1;
    if (($log10(123) != 0) && foo) bump <= bump + 1;
    if (($exp(123) != 0) && foo) bump <= bump + 1;
    if (($sqrt(123) != 0) && foo) bump <= bump + 1;
    if (($pow(123, 2) != 0) && foo) bump <= bump + 1;
    if (($floor(1.23) != 0) && foo) bump <= bump + 1;
    if (($ceil(1.23) != 0) && foo) bump <= bump + 1;
    if (($sin(123) != 0) && foo) bump <= bump + 1;
    if (($cos(123) != 0) && foo) bump <= bump + 1;
    if (($tan(123) != 0) && foo) bump <= bump + 1;
    if (($asin(123) != 0) && foo) bump <= bump + 1;
    if (($acos(123) != 0) && foo) bump <= bump + 1;
    if (($atan(123) != 0) && foo) bump <= bump + 1;
    if (($atan2(123, 2) != 0) && foo) bump <= bump + 1;
    if (($hypot(123, 2) != 0) && foo) bump <= bump + 1;
    if (($sinh(123) != 0) && foo) bump <= bump + 1;
    if (($cosh(123) != 0) && foo) bump <= bump + 1;
    if (($tanh(123) != 0) && foo) bump <= bump + 1;
    if (($asinh(123) != 0) && foo) bump <= bump + 1;
    if (($acosh(123) != 0) && foo) bump <= bump + 1;
    if (($atanh(123) != 0) && foo) bump <= bump + 1;
    if (($countbits(123, 2) != 0) && foo) bump <= bump + 1;
    if (($onehot(123) != 0) && foo) bump <= bump + 1;
    if ($isunknown(foo) && foo) bump <= bump + 1;
    if (($countones(123) != 0) && foo) bump <= bump + 1;
    if (($onehot0(123) != 0) && foo) bump <= bump + 1;
    if (($sampled(foo) != 0) && foo) bump <= bump + 1;
    if (($fell(foo) != 0) && foo) bump <= bump + 1;
    if (($changed(foo) != 0) && foo) bump <= bump + 1;
    if (($rose(foo) != 0) && foo) bump <= bump + 1;
    if (($stable(foo) != 0) && foo) bump <= bump + 1;
    if (($past(foo) != 0) && foo) bump <= bump + 1;
    if (($random != 0) && foo) bump <= bump + 1;
    if (($dist_erlang(result, 2, 3) != 0) && foo) bump <= bump + 1;
    if (($dist_normal(result, 2, 3) != 0) && foo) bump <= bump + 1;
    if (($dist_t(result, 2) != 0) && foo) bump <= bump + 1;
    if (($dist_chi_square(result, 2) != 0) && foo) bump <= bump + 1;
    if (($dist_exponential(result, 2) != 0) && foo) bump <= bump + 1;
    if (($dist_poisson(result, 2) != 0) && foo) bump <= bump + 1;
    if (($dist_uniform(result, 2, 3) != 0) && foo) bump <= bump + 1;
    if (($sformatf("abc") != "abc") && foo) bump <= bump + 1;
    if (foo && foo) bump <= bump + 1;
    cyc <= cyc + 1;
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
