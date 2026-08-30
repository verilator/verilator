// DESCRIPTION: Verilator: Test covergroup 'ref' formal bindings resolved per instance
// A covergroup reference formal is bound at construction, so a sample() reading through it
// names no design signal.  What each sample() may read is resolved from the handle it is
// called on where every write of that handle is a construction (x_inst, y_inst), and from the
// union over the covergroup type where it is not (z_alias, aliased from z_first).  Both must
// order the sample against the non-blocking writer of what it samples; only how much else they
// are ordered against differs.  Runs under --vltmt, where an unordered sample is a data race.
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  logic [1:0] siga;
  logic [1:0] sigb;
  logic [1:0] sigc;
  logic [1:0] sigd;

  covergroup cg_x(ref logic [1:0] sig);
    cp_x: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  covergroup cg_y(ref logic [1:0] sig);
    cp_y: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  covergroup cg_z(ref logic [1:0] sig);
    cp_z: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  // Constructed and sampled through the same handle: bindings are known exactly
  cg_x x_inst = new(siga);
  cg_y y_inst = new(sigb);

  // Two instances of one type, sampled through a handle that is assigned rather than
  // constructed, so the sample must assume either of them
  cg_z z_first = new(sigc);
  cg_z z_second = new(sigd);
  cg_z z_alias;

  initial z_alias = z_first;

  always @(posedge clk) x_inst.sample();
  always @(posedge clk) y_inst.sample();
  always @(posedge clk) z_alias.sample();

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    case (cyc)
      0: begin
        siga <= 2'b00;
        sigb <= 2'b01;
        sigc <= 2'b11;
        sigd <= 2'b00;
      end
      1: begin
        siga <= 2'b01;
        sigb <= 2'b01;
        sigc <= 2'b11;
        sigd <= 2'b01;
      end
      2: begin
        siga <= 2'b10;
        sigb <= 2'b01;
        sigc <= 2'b00;
        sigd <= 2'b10;
      end
      3: begin
        siga <= 2'b11;
        sigb <= 2'b10;
        sigc <= 2'b00;
        sigd <= 2'b11;
      end
      4: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase
  end
endmodule
