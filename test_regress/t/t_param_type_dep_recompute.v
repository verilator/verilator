// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Dependent value-param + type-param + value-param-of-type-param must be
// re-evaluated per specialization, not baked from the template default.
// Regression test for template poisoning in V3Param::cellPinCleanup: the
// normedNamep widthing block used to reach through a RefDType into the
// template's ParamTypeDType and constify its body, mutating the base
// module's dependent-param valuep so later specializations inherited the
// stale constant.  Three instances with distinct .width values in the
// same compilation catch any such cross-instance leakage.

module test #(
    parameter int width = 16,
    parameter int width2 = width + 8,
    parameter type data_t = logic [width2-1:0],
    parameter data_t data = data_t'(0)
) ();
  // Internal signal declared as the dependent type param, driven to
  // all-ones.  Post-fix, $bits and value readback must match the
  // spec's own resolved width, not the template default.
  data_t data_t_sig;
  initial data_t_sig = '1;
endmodule

module t;
  test #(.width(24), .data(32'h0)) inst_a ();
  test #(.width(16), .data(24'h0)) inst_b ();
  test #(.width( 8), .data(16'h0)) inst_c ();

  initial begin
    #1;
    // inst_a: width=24 -> width2=32 -> data_t is 32 bits
    if (inst_a.width2 !== 32) begin
      $write("%%Error inst_a.width2=%0d expected 32\n", inst_a.width2); $stop;
    end
    if ($bits(inst_a.data) !== 32) begin
      $write("%%Error $bits(inst_a.data)=%0d expected 32\n", $bits(inst_a.data)); $stop;
    end
    if (inst_a.data !== 32'h0) begin
      $write("%%Error inst_a.data=%h expected 0\n", inst_a.data); $stop;
    end
    if ($bits(inst_a.data_t_sig) !== 32) begin
      $write("%%Error $bits(inst_a.data_t_sig)=%0d expected 32\n",
             $bits(inst_a.data_t_sig)); $stop;
    end
    if (inst_a.data_t_sig !== 32'hFFFFFFFF) begin
      $write("%%Error inst_a.data_t_sig=%h expected FFFFFFFF\n",
             inst_a.data_t_sig); $stop;
    end

    // inst_b: width=16 -> width2=24 -> data_t is 24 bits
    if (inst_b.width2 !== 24) begin
      $write("%%Error inst_b.width2=%0d expected 24\n", inst_b.width2); $stop;
    end
    if ($bits(inst_b.data) !== 24) begin
      $write("%%Error $bits(inst_b.data)=%0d expected 24\n", $bits(inst_b.data)); $stop;
    end
    if (inst_b.data !== 24'h0) begin
      $write("%%Error inst_b.data=%h expected 0\n", inst_b.data); $stop;
    end
    if ($bits(inst_b.data_t_sig) !== 24) begin
      $write("%%Error $bits(inst_b.data_t_sig)=%0d expected 24\n",
             $bits(inst_b.data_t_sig)); $stop;
    end
    if (inst_b.data_t_sig !== 24'hFFFFFF) begin
      $write("%%Error inst_b.data_t_sig=%h expected FFFFFF\n",
             inst_b.data_t_sig); $stop;
    end

    // inst_c: width=8 -> width2=16 -> data_t is 16 bits
    if (inst_c.width2 !== 16) begin
      $write("%%Error inst_c.width2=%0d expected 16\n", inst_c.width2); $stop;
    end
    if ($bits(inst_c.data) !== 16) begin
      $write("%%Error $bits(inst_c.data)=%0d expected 16\n", $bits(inst_c.data)); $stop;
    end
    if (inst_c.data !== 16'h0) begin
      $write("%%Error inst_c.data=%h expected 0\n", inst_c.data); $stop;
    end
    if ($bits(inst_c.data_t_sig) !== 16) begin
      $write("%%Error $bits(inst_c.data_t_sig)=%0d expected 16\n",
             $bits(inst_c.data_t_sig)); $stop;
    end
    if (inst_c.data_t_sig !== 16'hFFFF) begin
      $write("%%Error inst_c.data_t_sig=%h expected FFFF\n",
             inst_c.data_t_sig); $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
