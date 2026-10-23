// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
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

  // Also elements of dynamically sized arrays in structs, with a wildcard index, and in arrays
  typedef struct {
    int aa[int];
    int da[];
    int q[$];
  } dyn_t;
  dyn_t bad_s;
  dyn_t bad_s7;
  int bad_wild[*];
  int bad_arr_aa[2][int];
  int bad_arr_da[2][];

  assign bad_s7.da[0] = 1;  // <--- Error: continuous dynarray element in struct

  always @(posedge clk) begin
    bad_s.aa[0] <= 2;  // Error: nonblocking associative array element in struct
    bad_s.da[0] <= 2;  // Error: nonblocking dynarray element in struct
    bad_s.q[0] <= 2;  // Error: nonblocking queue element in struct
    bad_s.da <= empty_dyn;  // OK: nonblocking dynarray assignment in struct, not to its element
    bad_wild[0] <= 2;  // Error: nonblocking wildcard associative array element
    bad_arr_aa[0][0] <= 2;  // Error: nonblocking associative array element in array
    bad_arr_da[0][0] <= 2;  // Error: nonblocking dynarray element in array
  end

  // Reading such elements is also not allowed in procedural continuous assignments
  int ok_r;
  initial begin
    // verilator lint_off IEEEMAYDEPRECATE
    assign ok_r = bad_s7.da[0];  // Error: continuous read of dynarray element in struct
    assign ok_r = bad_wild[0];  // Error: continuous read of wildcard associative array element
    assign ok_r = bad_arr_aa[0][0];  // Error: continuous read of associative array element in array
    // verilator lint_on IEEEMAYDEPRECATE
  end

  // Reading such elements in a nonblocking assignment is allowed, also to get a handle
  int ok_arr[2];
  Cls bad_arr_h[2][];
  dyn_t bad_arr_s[2];
  always @(posedge clk) begin
    ok_arr[bad_s.da[0]!=0] <= bad_s.da[1];  // OK: nonblocking, reads dynarray elements in struct
    ok_arr[bad_arr_aa[0][0]!=0] <= 2;  // OK: nonblocking, indexed by associative array element
    // Only the member is an error, as Verilator rejects NBAs to non-static class properties: the
    // pending update would have to keep the object alive (#7541). The dynarray element is only
    // read, to get the handle.
    bad_arr_h[0][0].m_bad2 <= 2;  // Error: nonblocking class automatic
    bad_arr_s[1].da[0] <= 2;  // Error: nonblocking dynarray element in struct in array
  end

  // Ports of automatic subroutines, including class methods, are automatic variables
  task automatic tbad(int bad_a, output int bad_o, ref int bad_r);
    bad_a <= 1;  // Error: nonblocking automatic task input
    bad_o <= 1;  // Error: nonblocking automatic task output
    bad_r <= 1;  // Error: nonblocking automatic task ref
    mt.o <= 1;  // OK: nonblocking static task output, by hierarchical reference
  endtask
  class ClsM;
    function void fbad(int bad_m);
      bad_m <= 1;  // Error: nonblocking class method argument
    endfunction
  endclass

endmodule
