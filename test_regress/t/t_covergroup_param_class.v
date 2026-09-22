// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

interface trace_if #(parameter int ILEN = 32, parameter int XLEN = 32) ();
  logic clk;
  logic [ILEN-1:0] insn;
endinterface

package cov_pkg;

  class TraceData #(parameter int ILEN = 32, parameter int XLEN = 32);
    logic [ILEN-1:0] insn;
  endclass

  class Instr #(parameter int ILEN = 32, parameter int XLEN = 32);
    TraceData #(ILEN, XLEN) current;
    function new();
      current = new();
    endfunction
  endclass

  class CovBase #(parameter int ILEN = 32, parameter int XLEN = 32);
    typedef Instr #(ILEN, XLEN) ins_t;

    // A virtual interface member is what puts an interface type reference
    // inside this class, alongside the covergroup below.
    virtual trace_if #(ILEN, XLEN) vif;

    covergroup cg with function sample(ins_t ins);
      cp_insn: coverpoint ins.current.insn {
        bins ecall = {32'h00000073};
      }
    endgroup

    function new(virtual trace_if #(ILEN, XLEN) vif);
      this.vif = vif;
      cg = new();
    endfunction

    function void do_sample();
      ins_t ins = new();
      ins.current.insn = 32'h00000073;
      cg.sample(ins);
    endfunction
  endclass

endpackage

import cov_pkg::*;

class Cov #(parameter int ILEN = 32, parameter int XLEN = 32)
  extends CovBase #(ILEN, XLEN);
  function new(virtual trace_if #(ILEN, XLEN) vif);
    super.new(vif);
  endfunction
endclass

module worker(trace_if vif);
  // Specialized from parameters read off the interface instance
  Cov #(vif.ILEN, vif.XLEN) cov;
  initial begin
    cov = new(vif);
    cov.do_sample();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module t;
  trace_if #(32, 64) vif();
  worker worker(vif);
endmodule
