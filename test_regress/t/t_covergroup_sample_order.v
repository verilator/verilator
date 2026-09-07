// DESCRIPTION: Verilator: Test covergroup sample() scheduling against non-blocking writers
// A coverpoint must observe the value its signal had before the sampling edge's non-blocking
// assignments commit, whether sampling is automatic, manual, through a 'ref' formal, or of a
// combinationally derived signal.  Runs under --vltmt as well: none of these reads are
// visible at the sample() call site, so each is also a data race if left unordered.
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  logic [1:0] data;
  logic [1:0] refsig;
  logic [1:0] derived;

  assign derived = data + 2'b01;

  // Automatic sampling, coverpoint straight on a non-blocking driven signal
  covergroup cg_auto @(posedge clk);
    cp_auto: coverpoint data {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  // Automatic sampling, coverpoint on a combinationally derived signal
  covergroup cg_derived @(posedge clk);
    cp_derived: coverpoint derived {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  // Manual sampling, coverpoint reached through a 'ref' formal argument
  covergroup cg_ref(ref logic [1:0] sig);
    cp_ref: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  cg_auto auto_cg = new;
  cg_derived derived_cg = new;
  cg_ref ref_cg = new(refsig);

  int cyc = 0;

  // Manual sample() from its own process, so it is not ordered by being in the writer's block
  always @(posedge clk) ref_cg.sample();

  always @(posedge clk) begin
    cyc <= cyc + 1;

    case (cyc)
      0: begin
        data   <= 2'b00;
        refsig <= 2'b00;
      end
      1: begin
        data   <= 2'b01;
        refsig <= 2'b01;
      end
      2: begin
        data   <= 2'b10;
        refsig <= 2'b10;
      end
      3: begin
        data   <= 2'b11;
        refsig <= 2'b11;
      end
      4: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase
  end
endmodule
