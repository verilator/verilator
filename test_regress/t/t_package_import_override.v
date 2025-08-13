// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;

  typedef enum logic [1:0] {
    INT,
    BLA,
    DUMMY
  } t_shadowed_enum;

endpackage

module sub
  import pkg::*;
(
    input logic INT,  // This is also in the pkg::t_shadowed_enum, but it shadows it
    output logic dummy_out
);

  assign dummy_out = !INT;
endmodule

module t;
  logic my_wire;
  logic dummy_out;

  sub i_sub (
      .INT(my_wire),
      .dummy_out(dummy_out)
  );

  initial begin
    my_wire = 1'b0;

    repeat (2) begin
      my_wire = ~my_wire;
      #1ns;
      $display("my_wire = %b, dummy_out = %b", my_wire, dummy_out);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
