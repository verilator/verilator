// DESCRIPTION: Verilator: Test covergroup 'ref' bindings where no handle is a plain variable
// Companion to t_covergroup_ref_bind, which covers the resolvable shapes.  Here nothing is a
// plain variable: the covergroup is constructed into an array element, sampled through an array
// element, and the 'ref' actual is an array element too.  So neither the construction nor the
// sample names one covergroup object, and both must fall back to the union over the covergroup
// type -- which must still order every sample against the non-blocking writer of what any
// instance of that type reads.  cg_b repeats that with a struct member as the handle instead of
// an array element.  Runs under --vltmt, where an unordered sample is a data race,
// and with -fno-lift-expr, which leaves the construction assigning directly to the array
// element instead of to a lifted temporary.
// This file ONLY is placed into the Public Domain, for any use, without warranty.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  logic [1:0] sigs[2];
  logic [1:0] sigt[2];

  covergroup cg_a(ref logic [1:0] sig);
    cp_a: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  covergroup cg_b(ref logic [1:0] sig);
    cp_b: coverpoint sig {
      bins zero = {2'b00}; bins one = {2'b01}; bins two = {2'b10}; bins three = {2'b11};
    }
  endgroup

  cg_a arr[2];

  typedef struct {
    cg_b cg;
  } struct_t;

  struct_t s0;
  struct_t s1;

  // The construction destination is an array element, so there is no handle to key the
  // bindings on and every instance of cg_a must assume both of them.  The 'ref' actual is an
  // array element as well, and binds the array it selects from.
  initial begin
    arr[0] = new(sigs[0]);
    arr[1] = new(sigs[1]);
  end

  // Same shape again with a struct member holding the handle: the construction destination and
  // the sample receiver are both member selects, so neither names one covergroup object
  initial s0.cg = new(sigt[0]);
  initial s1.cg = new(sigt[1]);

  // The sample receiver is an array element, so it names no one covergroup object either
  always @(posedge clk) arr[0].sample();
  always @(posedge clk) arr[1].sample();
  always @(posedge clk) s0.cg.sample();
  always @(posedge clk) s1.cg.sample();

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    case (cyc)
      0: begin
        sigs[0] <= 2'b01;
        sigs[1] <= 2'b11;
      end
      1: begin
        sigs[0] <= 2'b10;
        sigs[1] <= 2'b11;
      end
      2: begin
        sigs[0] <= 2'b11;
        sigs[1] <= 2'b10;
      end
      3: begin
        sigs[0] <= 2'b11;
        sigs[1] <= 2'b00;
      end
      4: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase
  end

  // What the struct-held covergroups read, written in a block of its own so that leaving their
  // samples unordered against it is a data race on its own
  always @(posedge clk) begin
    case (cyc)
      0: begin
        sigt[0] <= 2'b01;
        sigt[1] <= 2'b10;
      end
      1: begin
        sigt[0] <= 2'b10;
        sigt[1] <= 2'b11;
      end
      2: begin
        sigt[0] <= 2'b11;
        sigt[1] <= 2'b11;
      end
      3: begin
        sigt[0] <= 2'b00;
        sigt[1] <= 2'b01;
      end
      default: ;
    endcase
  end
endmodule
