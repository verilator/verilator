// DESCRIPTION: Verilator: Test covergroup sample() called from combinational logic
// A sample() reads what the covergroup holds, whether the covergroup reaches those signals
// through a 'ref' formal or names them directly, and those reads happen as part of the block
// that calls sample().  They must be recorded for the multi-threaded data hazard fixer, but
// they must not be given the consumer edge a combinational read normally gets: that edge is
// what a sensitivity list produces, and the calling block is not sensitive to what the
// covergroup samples.
// Here each calling block is combinational and drives the signal the sampled one is derived
// from, so giving those reads a combinational consumer edge closes a loop through the
// OrderGraph.  Nothing before ordering sees such a loop, so it is not broken beforehand, and
// V3Order fails with 'Circular logic when ordering code' rather than coping with it.
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;

  // Sampled through a 'ref' formal, so the sampling block holds no reference to 'ref_gnt'
  logic [1:0] ref_req;
  logic [1:0] ref_gnt;

  // Sampled by a coverpoint naming it, so the reference is in sample(), not in the block
  logic [1:0] dir_req;
  logic [1:0] dir_gnt;

  covergroup cg_ref (ref logic [1:0] sig);
    cp_ref: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  covergroup cg_direct;
    cp_direct: coverpoint dir_gnt {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  cg_ref ref_cg = new(ref_gnt);
  cg_direct direct_cg = new;

  // What is sampled, combinationally derived from what the sampling block drives
  assign ref_gnt = ref_req ^ 2'b01;

  always_comb begin
    dir_gnt = 2'b00;
    if (dir_req[0]) dir_gnt = 2'b11;
    if (dir_req[1]) dir_gnt = 2'b01;
  end

  // Sampling from combinational logic.  Neither block is sensitive to what its sample() reads,
  // so both loops would be ones ordering introduces rather than ones the source describes.
  // What each sample() observes here therefore follows from how ordering resolved the loop --
  // see the .py for what that means for the golden.
  always_comb begin
    case (cyc[1:0])
      2'd0: ref_req = 2'b00;
      2'd1: ref_req = 2'b01;
      2'd2: ref_req = 2'b10;
      default: ref_req = 2'b11;
    endcase
    ref_cg.sample();
  end

  always_comb begin
    case (cyc[1:0])
      2'd0: dir_req = 2'b00;
      2'd1: dir_req = 2'b01;
      2'd2: dir_req = 2'b10;
      default: dir_req = 2'b11;
    endcase
    direct_cg.sample();
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
