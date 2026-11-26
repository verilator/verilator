// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Methods defined by IEEE:
//    function int unsigned $urandom [ (int seed ) ] ;
//     function int unsigned $urandom_range( int unsigned maxval,
//                                           int unsigned minval = 0 );

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
`ifndef VERILATOR
  `define PROC
`endif
`ifdef PROC
  process p;
`endif

  int unsigned v1;
  int unsigned v2;
  int unsigned v3;
  string s;

  initial begin
`ifdef PROC
    if (p != null) $stop;
    p = process::self();
`endif

    v1 = $urandom;
    v2 = $urandom;
    v3 = $urandom();
    if (v1 == v2 && v1 == v3) $stop;  // Possible, but 2^-64

    // Range
    v2 = $urandom_range(v1, v1);
    if (v1 != v2) $stop;

    v2 = $urandom_range(0, 32'hffffffff);
    if (v2 == v1) $stop;

    for (int test = 0; test < 20; ++test) begin
      v1 = 2;
      v1 = $urandom_range(0, v1);
      if (v1 != 0 && v1 != 1 && v1 != 2) $stop;
      v1 = $urandom_range(2, 0);
      if (v1 != 0 && v1 != 1 && v1 != 2) $stop;
      v1 = $urandom_range(3);
      if (v1 != 0 && v1 != 1 && v1 != 2 && v1 != 3) $stop;
    end

    // Seed stability
    // Note UVM doesn't use $urandom seeding
    v1 = $urandom(1);
    v2 = $urandom(1);
    if (v1 != v2) $stop;
    v2 = $urandom(1);
    if (v1 != v2) $stop;

    begin
      // Two calls draw twice, also when extended wider than 64 bits
      int unsigned r1;
      int unsigned r2;
      int unsigned r3;
      bit [79:0] w80;
      void'($urandom(1));
      r1 = $urandom();
      r2 = $urandom();
      r3 = $urandom();
      void'($urandom(1));
      w80 = 80'({$urandom(), $urandom()});
      v2 = $urandom();
      `checkh(w80[79:64], 16'h0);
      `checkh(v2, r3);
      `checkd(w80[63:0] == {r1, r2} || w80[63:0] == {r2, r1}, 1'b1);
    end
    begin
      // Likewise not extended
      int unsigned r1;
      int unsigned r2;
      int unsigned r3;
      bit [63:0] r64;
      void'($urandom(1));
      r1 = $urandom();
      r2 = $urandom();
      r3 = $urandom();
      void'($urandom(1));
      r64 = {$urandom(), $urandom()};
      v2 = $urandom();
      `checkh(v2, r3);
      `checkd(r64 == {r1, r2} || r64 == {r2, r1}, 1'b1);
    end
    begin
      // A seeded $random call updates its seed, also when concatenated
      int seed;
      bit [63:0] r64;
      seed = 7;
      r64 = {$random(seed), $random()};
      `checkd(seed != 7, 1'b1);
      seed = 7;
      r64 = {$random(), $random(seed)};
      `checkd(seed != 7, 1'b1);
    end
`ifdef VERILATOR
    // Reseeding with $urandom(seed) also restarts the sequence of $random
    begin
      // Two concatenated $random calls draw one 64-bit value, as an optimization deviating
      // from IEEE 1800-2023 11.3.5, extended wider than 64 bits or not
      int unsigned r1;
      int unsigned r2;
      bit [63:0] r64;
      bit [79:0] w80;
      void'($urandom(1));
      r1 = $random();
      r2 = $random();
      void'($urandom(1));
      r64 = {$random(), $random()};
      v1 = $random();
      void'($urandom(1));
      w80 = 80'({$random(), $random()});
      v2 = $random();
      `checkh(v1, r2);
      `checkh(w80, 80'(r64));
      `checkh(v2, r2);
    end
    begin
      // A $random call and a $urandom call each draw
      int unsigned r3;
      bit [63:0] r64;
      void'($urandom(1));
      v1 = $random();
      v2 = $urandom();
      r3 = $random();
      void'($urandom(1));
      r64 = {$random(), $urandom()};
      `checkd(r64 == {v1, v2} || r64 == {v2, v1}, 1'b1);
      v2 = $random();
      `checkh(v2, r3);
    end
`endif

`ifdef PROC
    // Seed stability via process.srandom
    p.srandom(1);
    v1 = $urandom();
    p.srandom(1);
    v2 = $urandom();
    if (v1 != v2) $stop;
    p.srandom(1);
    v2 = $urandom();
    if (v1 != v2) $stop;

    // Seed stability via process.srandom
    p.srandom(32'h88888888);  // "Large" seed to check a VlRNG::srandom edge case
    v1 = $urandom();
    p.srandom(32'h88888888);
    v2 = $urandom();
    if (v1 != v2) $stop;
    p.srandom(32'h88888888);
    v2 = $urandom();
    if (v1 != v2) $stop;

    // Seed stability via process.get_randstate
    s = p.get_randstate();
    v1 = $urandom();
    p.set_randstate(s);
    v2 = $urandom();
    if (v1 != v2) $stop;
    p.set_randstate(s);
    v2 = $urandom();
    if (v1 != v2) $stop;
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
