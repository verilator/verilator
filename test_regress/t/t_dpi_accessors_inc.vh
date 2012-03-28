// DESCRIPTION: Verilator: Accessor definitions for test of DPI accessors
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by Jeremy Bennett and Jie Xu

// See t_dpi_accessors.v for details of the test. This file should be included
// by the top level module to define all the accessors needed.

   // Use the macros to provide the desire access to our data. First simple
   // access to the registers, array elements and wires. For consistency with
   // simulators, we do not attempt to write wires.
   `RW_ACCESS ([0:0], a,     {t.i_test_sub.a});
   `RW_ACCESS ([7:0], b,     {t.i_test_sub.b});
   `RW_ACCESS ([7:0], mem32, {t.i_test_sub.mem[32]});
   `R_ACCESS  ([0:0], c,     {t.i_test_sub.c});
   `R_ACCESS  ([7:0], d,     {t.i_test_sub.d});
   `RW_ACCESS ([7:0], e,     {t.i_test_sub.e});
   `RW_ACCESS ([7:0], f,     {t.i_test_sub.f});

    // Slices of vectors and array elements. For consistency with simulators,
    // we do not attempt to write wire slices.
    `RW_ACCESS ([3:0], b_slice, {t.i_test_sub.b[3:0]});
    `RW_ACCESS ([4:0], mem32_slice,
		{t.i_test_sub.mem[32][7:6],t.i_test_sub.mem[32][2:0]});
    `R_ACCESS  ([5:0], d_slice, {t.i_test_sub.d[6:1]});

    // Complex registers, one with distinct read and write. We avoid use of
    // wires for consistency with simulators.
    `RW_ACCESS ([14:0], l1, {t.i_test_sub.b[3:0],
			    t.i_test_sub.mem[32][7:6],
			    t.i_test_sub.e[6:1],
			    t.i_test_sub.mem[32][2:0]});
    `R_ACCESS ([7:0], l2, {t.i_test_sub.e[7:4], t.i_test_sub.f[3:0]});
    `W_ACCESS ([7:0], l2, {t.i_test_sub.e[5:2], t.i_test_sub.f[5:2]});
