// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2020 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;

  logic [2:0] sig0[3];
  logic [2:0] sig1[3][2];
  bit [2:0] sig2[3][3];

  import "DPI-C" function void import_func0(input logic [3:0] in[0:2]);
  import "DPI-C" function void import_func1(input logic [2:0] in[0:2]);
  import "DPI-C" function void import_func2(input logic [2:0] in[0:2][0:2]);

  initial begin
    // packed width differs
    import_func0(sig0);
    // dimension differs
    import_func1(sig1);
    // unpacked extent differs
    import_func2(sig1);
    // bit v.s. logic mismatch
    import_func2(sig2);
    // packed var for unpacked port
    import_func0(sig0[1]);
  end

  typedef struct {int a;} s_t;
  typedef struct {byte b;} u_t;
  u_t sig3[3];

  import "DPI-C" function void import_func3(input s_t in[0:2]);

  initial begin
    // unpacked structure type differs
    import_func3(sig3);
    // unpacked structure v.s. packed
    import_func3(sig0);
    // packed v.s. unpacked structure
    import_func0(sig3);
  end

  import "DPI-C" function void import_func4(output byte out[]);
  byte dyn[];
  byte que[$];

  initial begin
    // dynamic array or queue for an output open array
    import_func4(dyn);
    import_func4(que);
  end

  import "DPI-C" function void import_func5(input real in[]);
  import "DPI-C" function void import_func6(input int in[]);
  import "DPI-C" function void import_func7(input real in[][2]);
  int ints[2];
  real reals[];
  int ints32[3][2];
  int ints_dyn[3][];
  class Cls;
  endclass
  Cls objs[];

  initial begin
    // elements not of an equivalent type for an open array
    import_func5(ints);
    import_func6(reals);
    import_func7(ints32);
    import_func6(objs);
    import_func6(sig3);
    import_func6(ints_dyn);
  end

  import "DPI-C" function void import_func8(input byte in[]);
  byte assoc[int];
  byte wild[*];

  initial begin
    // associative arrays for an open array
    import_func8(assoc);
    import_func8(wild);
  end

  import "DPI-C" function void import_func9(input bit [] in[]);
  bit [7:0] bits_dyn[3][];

  initial begin
    // fewer unpacked dimensions, not counting the unsized packed dimension
    import_func9(bits_dyn);
  end
endmodule
