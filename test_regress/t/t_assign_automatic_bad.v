// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// 6.21 Scope and lifetime
// Automatic variables and elements of dynamically sized array variables shall
// not be written with nonblocking, continuous, or procedural continuous
// assignments. Non-static class properties shall not be written with continuous
// or procedural continuous assignments.

class Cls;
  static int s_ok1;
  static int s_ok2;
  static int s_dyn[];
  int m_bad1;
  int m_bad2;
endclass

module t (
    input clk
);

  Cls c;

  int bad_dyn5[];
  int bad_dyn6[];
  int empty_dyn[];
  int empty_queue[$];
  int empty_assoc[int];
  int bad_queue[$];
  int bad_assoc[int];
  Cls clist[1];

  assign bad_dyn5[0] = empty_dyn;  // <--- Error: continuous dynarray element
  assign bad_dyn5 = empty_dyn;  // <--- OK: continuous dynarray assignment, not to its element
  assign c.m_bad1 = 2;  // <--- Error: continuous class non-static
  // Only one simulator fails on this, probably not legal
  // assign Cls::s_ok1 = 2;  // OK: continuous class static

  logic ok_7;
  task mt(output o);  // OK: function output
    o <= 1;
  endtask

  always @(posedge clk) begin
    bad_dyn6[0] <= 2;  // <--- Error: nonblocking dynarray element
    bad_dyn6 <= empty_dyn;  // <--- OK: nonblocking dynarray assignment, not to its element
    bad_queue[0] <= 2;  // Error: nonblocking queue element assignment
    bad_queue <= empty_queue;  // OK: nonblocking assignment to queue itself, not to its element
    bad_assoc[0] <= 2;  // Error: nonblocking associative array element assignment
    bad_assoc <= empty_assoc; // OK: nonblocking assignment to associative array itself, not to its element
    Cls::s_ok2 <= 2;  // OK: nonblocking class static
    c.m_bad2 <= 2;  // <--- Error: nonblocking class automatic
    Cls::s_dyn <= 2;  // OK: nonblocking class static dynarray assignment, not to its element
    Cls::s_dyn[0] <= 2;  // Error: nonblocking class static dynarray element
    clist[
    bad_dyn6[0]++
    ].s_dyn <= '1;  // OK: direct nonblocking assignment to dynamically-sized array
    clist[
    bad_dyn6[0]++
    ].s_dyn[0] <= '1;  // Error: nonblocking assigment to dynamically-sized array element
    mt(ok_7);
    $stop;
  end

endmodule
