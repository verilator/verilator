// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Michael Taylor.
// SPDX-License-Identifier: CC0-1.0

module issue #(
  parameter int els_p = 1,
  // Parameter array of length els_p
  parameter int val_p [els_p-1:0],
  // The original number of elements in the top-level array.  This is
  // used to compute the expected value in each instance for self-checking.
  parameter int orig_els = 1
) ();
  // Recursive instantiation: create a smaller issue if there are
  // more than one element.  Select all but the lowest element of val_p.
  if (els_p > 1) begin : r
    issue #(
      .els_p(els_p-1),
      .val_p(val_p[els_p-1:1]),
      .orig_els(orig_els)
    ) x ();
  end
  // Self-check: compute the expected value based on the original array size
  // (orig_els) and the current size (els_p).  The lowest element of the
  // parameter array should equal orig_els - els_p + 1.  If not, print an
  // error.  Regardless, display the value and the instance name for
  // debugging.  Use an 8-digit hex for consistency.
  initial begin
    int expected;
    expected = orig_els - els_p + 1;
    if (val_p[0] !== expected) begin
       $error("Wrong value %0d expected %0d in %m", val_p[0], expected);
       $finish;
    end
    $display("%08x (%m)", val_p[0]);
  end
endmodule

module t ();
  // Define a parameter array of integers.  The unpacked array range is
  // 5-1:0 (4 downto 0), giving 5 elements with values 5,4,3,2,1.  Each
  // nested instance of issue will
  // slice off one element from the high end, so the printed values will
  // be 1,2,3,4,5 in that order.
  parameter int val_p [5-1:0] = '{5,4,3,2,1};
  issue #(
    .els_p(5),
    .val_p(val_p),
    .orig_els(5)
  ) iss ();
  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
