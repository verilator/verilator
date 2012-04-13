// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2012 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.
//
// Contributed by Jeremy Bennett and Jie Xu
//
//*************************************************************************

#include <iostream>
#include <iomanip>

#include "svdpi.h"

#include "Vt_dpi_accessors.h"
#include "Vt_dpi_accessors__Dpi.h"


using std::cout;
using std::dec;
using std::endl;
using std::hex;
using std::setfill;
using std::setw;


// Convenience function to check we didn't finish unexpectedly
static void
checkFinish (const char *msg)
{
    if (Verilated::gotFinish ()) {
	vl_fatal (__FILE__, __LINE__, "dut", msg);
	exit (1);
    }
}	// checkFinish ()


// Convenience function to log the value of a register in hex. Only in verbose
// mode.
static void
logReg (int         clk,
	   const char *desc,
	   int         val,
	   const char *note)
{
#ifdef TEST_VERBOSE
    cout << "clk = " << clk << ", " << desc << " = " << val << note << endl;
#endif
}	// logReg ()


// Convenience function to log the value of a register in hex. Only in verbose
// mode.
static void
logRegHex (int         clk,
	   const char *desc,
	   int         bitWidth,
	   int         val,
	   const char *note)
{
#ifdef TEST_VERBOSE
    cout << "clk = " << clk << ", " << desc << " = " << bitWidth << "\'h" << hex
	 << setw ((bitWidth - 1) / 4 + 1) << setfill ('0') << val
	 << setfill (' ') << setw (0) << dec << note << endl;
#endif

}	// logRegHex ()


// Convenience function to check we got an expected result. Silent on success.
static void
checkResult (bool    p,
	     const char *msg_fail)
{
    if (!p) {
	vl_fatal (__FILE__, __LINE__, "dut", msg_fail);
    }
}	// checkResult ()


// Main function instantiates the model and steps through the test.
int main ()
{
    Vt_dpi_accessors *dut = new Vt_dpi_accessors ("dut");
    svSetScope (svGetScopeFromName ("dut.v"));

    // evaluate the model with no signal changes to get the initial blocks
    // executed.
    dut->eval ();

#ifdef TEST_VERBOSE
    cout << "Initial DPI values" << endl;
    cout << "==================" << endl;
#endif

    int  a     = (int) a_read ();
    int  b     = (int) b_read ();
    int  mem32 = (int) mem32_read ();
    int  c     = (int) c_read ();
    int  d     = (int) d_read ();
    int  e     = (int) e_read ();
    int  f     = (int) f_read ();

#ifdef TEST_VERBOSE
    cout << "Read  a     = " << a << endl;
    cout << "Read  b     = 8'h" << hex << setw (2) << setfill ('0') << b
	 << setfill (' ') << setw (0) << dec << endl;
    cout << "Read  mem32 = 8'h" << hex << setw (2) << setfill ('0') << mem32
	 << setfill (' ') << setw (0) << dec << endl;
    cout << "Read  c     = " << c << endl;
    cout << "Read  d     = 8'h" << hex << setw (2) << setfill ('0') << d
	 << setfill (' ') << setw (0) << dec << endl;
    cout << "Read  e     = 8'h" << hex << setw (2) << setfill ('0') << e
	 << setfill (' ') << setw (0) << dec << endl;
    cout << "Read  f     = 8'h" << hex << setw (2) << setfill ('0') << f
	 << setfill (' ') << setw (0) << dec << endl;
    cout << endl;
#endif

    checkResult ((0 == a) && (0x00 == b) && (0x20 == mem32) && (1    == c)
		 && (0xff == d) && (0x00 == e) && (0x00 == f),
		 "Bad initial DPI values.");

    // Initialize the clock
    dut->clk = 0;

    // Check we can read a scalar register.
#ifdef TEST_VERBOSE
    cout << "Test of scalar register reading" << endl;
    cout << "===============================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	a = (int) a_read ();
	logReg (dut->clk, "read a", a, " (before clk)");
	dut->eval ();

	int  a_after = (int) a_read ();
	logReg (dut->clk, "read a", a_after, " (after clk)");
#ifdef TEST_VERBOSE
	cout << endl;
#endif
	// On a posedge, a should toggle, on a negedge it should stay the
	// same.
	checkResult (   ((dut->clk == 1) && (a_after == (1 - a)))
		     || ((dut->clk == 0) && (a_after ==  a     )),
		     "Test of scalar register reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can read a vector register.
#ifdef TEST_VERBOSE
    cout << "Test of vector register reading" << endl;
    cout << "===============================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	b = (int) b_read ();
	logRegHex (dut->clk, "read b", 8, b, " (before clk)");

	dut->eval ();

	int  b_after = (int) b_read ();
	logRegHex (dut->clk, "read b", 8, b_after, " (after clk)");
	// b should increment on a posedge and stay the same on a negedge.
	checkResult (   ((dut->clk == 1) && (b_after == (b + 1)))
		     || ((dut->clk == 0) && (b_after ==  b     )),
		     "Test of vector register reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Test we can read an array element
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of array element reading" << endl;
    cout << "=============================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	mem32 = (int) mem32_read ();
	logRegHex (dut->clk, "read mem32", 8, mem32, " (before clk)");

	dut->eval ();

	mem32 = (int) mem32_read ();
	logRegHex (dut->clk, "read mem32", 8, mem32, " (after clk)");

	// In this case, the value never changes. But we should check it is
	// waht we expect (0x20).
	checkResult (mem32 == 0x20, "Test of array element reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can read a scalar wire
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of scalar wire reading" << endl;
    cout << "===========================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	a = (int) a_read ();
	c = (int) c_read ();
	logReg (dut->clk, "read a", a, " (before clk)");
	logReg (dut->clk, "read c", c, " (before clk)");

	dut->eval ();

	a = (int) a_read ();
	c = (int) c_read ();
	logReg (dut->clk, "read a", a, " (after clk)");
	logReg (dut->clk, "read c", c, " (after clk)");
	// "c" is continuously assigned as the inverse of "a", but in
	// Verilator, that means that it will only change value when "a"
	// changes on the posedge of a clock. Put simply, "c" always holds the
	// inverse of the "after clock" value of "a".
	checkResult (c == (1 - a), "Test of scalar wire reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can read a vector wire
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of vector wire reading" << endl;
    cout << "===========================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	b = (int) b_read ();
	d = (int) d_read ();
	logRegHex (dut->clk, "read b", 8, b, " (before clk)");
	logRegHex (dut->clk, "read d", 8, d, " (before clk)");

	dut->eval ();

	b = (int) b_read ();
	d = (int) d_read ();
	logRegHex (dut->clk, "read b", 8, b, " (after clk)");
	logRegHex (dut->clk, "read d", 8, d, " (after clk)");

	// "d" is continuously assigned as the (8-bit) bitwise inverse of "b",
	// but in Verilator, that means that it will only change value when
	// "b" changes on the posedge of a clock. Put simply, "d" always holds
	// the inverse of the "after clock" value of "b".
	checkResult (d == ((~b) & 0xff), "Test of vector wire reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can write a scalar register
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of scalar register writing" << endl;
    cout << "===============================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	a = 1 - (int) a_read ();
	a_write (a);
	logReg (dut->clk, "write a", a, " (before clk)");
	a = a_read ();
	logReg (dut->clk, "read  a", a, " (before clk)");

	dut->eval ();

	int  a_after = (int) a_read ();
	logReg (dut->clk, "read  a", a_after, " (after clk)");

	// On a posedge clock, the value of a that is written should toggle,
	// on a negedge, it should not.
	checkResult (   ((dut->clk == 1) && (a_after == (1 - a)))
		     || ((dut->clk == 0) && (a_after ==  a     )),
		     "Test of scalar register writing failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can write a vector register
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of vector register writing" << endl;
    cout << "===============================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	b = (int) b_read () - 1;
	b_write ((const svBitVecVal *) &b);
	logRegHex (dut->clk, "write b", 8, b, " (before clk)");
	b = (int) b_read ();
	logRegHex (dut->clk, "read  b", 8, b, " (before clk)");

	dut->eval ();

	int  b_after = (int) b_read ();
	logRegHex (dut->clk, "read  b", 8, b_after, " (after clk)");

	// The value of "b" written should increment on a posedge and stay the
	// same on a negedge.
	checkResult (   ((dut->clk == 1) && (b_after == (b + 1)))
		     || ((dut->clk == 0) && (b_after ==  b     )),
		     "Test of vector register writing failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Test we can write an array element
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of array element writing" << endl;
    cout << "=============================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	mem32 = (int) mem32_read () - 1;
	mem32_write ((const svBitVecVal *) &mem32);
	logRegHex (dut->clk, "write mem32", 8, mem32, " (before clk)");
	mem32 = (int) mem32_read ();
	logRegHex (dut->clk, "read  mem32", 8, mem32, " (before clk)");

	dut->eval ();

	int  mem32_after = (int) mem32_read ();
	logRegHex (dut->clk, "read  mem32", 8, mem32_after, " (after clk)");

	// In this case, the value we write never changes (this would only
	// happen if this part of the test coincided with the 32nd element
	// being overwritten, which it does not. Check that the value after
	// the clock is the same as before the clock.
	checkResult (mem32_after == mem32,
		     "Test of array element writing failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can read a vector register slice
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of vector register slice reading" << endl;
    cout << "=====================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	b            = (int) b_read ();
	int  b_slice = (int) b_slice_read ();
	logRegHex (dut->clk, "read b [7:0]", 8, b,       " (before clk)");
	logRegHex (dut->clk, "read b [3:0]", 4, b_slice, " (before clk)");

	dut->eval ();

	b       = (int) b_read ();
	b_slice = (int) b_slice_read ();
	logRegHex (dut->clk, "read b [7:0]", 8, b,       " (after clk)");
	logRegHex (dut->clk, "read b [3:0]", 4, b_slice, " (after clk)");

	// The slice of "b" should always be the bottom 4 bits of "b"
	checkResult (b_slice == (b & 0x0f),
		     "Test of vector register slice reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Test we can read an array element slice
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of array element slice reading" << endl;
    cout << "===================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	mem32            = (int) mem32_read ();
	int  mem32_slice = (int) mem32_slice_read ();
	logRegHex (dut->clk, "read mem32 [7:0]    ", 8, mem32, " (before clk)");
	logRegHex (dut->clk, "read mem32 [7:6,2:0]", 5, mem32_slice,
		   " (before clk)");

	dut->eval ();

	mem32       = (int) mem32_read ();
	mem32_slice = (int) mem32_slice_read ();
	logRegHex (dut->clk, "read mem32 [7:0]    ", 8, mem32," (after clk)");
	logRegHex (dut->clk, "read mem32 [7:6,2:0]", 5, mem32_slice,
		   " (after clk)");

	// The slice of "mem32" should always be the concatenation of the top
	// 2 and bottom 3 bits of "mem32"
	checkResult (mem32_slice == (((mem32 & 0xc0) >> 3) | (mem32 & 0x07)),
		     "Test of array element slice reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can read a vector wire slice
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of vector wire slice reading" << endl;
    cout << "=================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;
	b           = (int) b_read ();
	d           = (int) d_read ();
	int d_slice = (int) d_slice_read ();
	logRegHex (dut->clk, "read b [7:0]", 8, b,       " (before clk)");
	logRegHex (dut->clk, "read d [7:0]", 8, d,       " (before clk)");
	logRegHex (dut->clk, "read d [6:1]", 6, d_slice, " (before clk)");

	dut->eval ();

	b       = (int) b_read ();
	d       = (int) d_read ();
	d_slice = (int) d_slice_read ();
	logRegHex (dut->clk, "read b [7:0]", 8, b,       " (after clk)");
	logRegHex (dut->clk, "read d [7:0]", 8, d,       " (after clk)");
	logRegHex (dut->clk, "read d [6:1]", 6, d_slice, " (after clk)");

	// The slice of "d" should always be the middle 6 bits of "d".
	checkResult (d_slice == ((d & 0x7e) >> 1),
		     "Test of vector wire slice reading failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can write a vector register slice
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of vector register slice writing" << endl;
    cout << "=====================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;

	b            = (int) b_read ();
	int  b_slice = (int) b_slice_read ();
	logRegHex (dut->clk, "read  b [7:0]", 8, b,       " (before write)");
	logRegHex (dut->clk, "read  b [3:0]", 4, b_slice, " (before write)");

	b_slice--;
	b_slice_write ((const svBitVecVal *) &b_slice);
	logRegHex (dut->clk, "write b [3:0]", 4, b_slice, " (before clk)");

	int  b_after       = (int) b_read ();
	int  b_slice_after = (int) b_slice_read ();
	logRegHex (dut->clk, "read  b [7:0]", 8, b_after,
		   " (before clk)");
	logRegHex (dut->clk, "read  b [3:0]", 4, b_slice_after,
		   " (before clk)");

	// We must test that when we wrote the slice of "b", we only wrote the
	// correct bits. The slice of b is b[3:0]
	int  b_new = (b & 0xf0) | (b_slice &0x0f);
	checkResult (b_after == b_new,
		     "Test of vector register slice writing failed.");

	dut->eval ();

	b       = (int) b_read ();
	b_slice = (int) b_slice_read ();
	logRegHex (dut->clk, "read  b [7:0]", 8, b,       " (after clk)");
	logRegHex (dut->clk, "read  b [3:0]", 4, b_slice, " (after clk)");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Test we can write an array element slice
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of array element slice writing" << endl;
    cout << "===================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;

	mem32            = (int) mem32_read ();
	int  mem32_slice = (int) mem32_slice_read ();
	logRegHex (dut->clk, "read  mem32 [7:0]    ", 8, mem32,
		   " (before write)");
	logRegHex (dut->clk, "read  mem32 [7:6,2:0]", 5, mem32_slice,
		   " (before write)");

	mem32_slice--;
	mem32_slice_write ((const svBitVecVal *) &mem32_slice);
	logRegHex (dut->clk, "write mem32 [7:6,2:0]", 5, mem32_slice,
		   " (before clk)");

	int  mem32_after       = (int) mem32_read ();
	int  mem32_slice_after = (int) mem32_slice_read ();
	logRegHex (dut->clk, "read  mem32 [7:0]    ", 8, mem32_after,
		   " (before clk)");
	logRegHex (dut->clk, "read  mem32 [7:6,2:0]", 5, mem32_slice_after,
		   " (before clk)");

	// We must test that when we wrote the slice of "mem32", we only wrote
	// the correct bits. The slice of "mem32" is {mem32[7:6], mem32[2:0]}.
	int  mem32_new =   (mem32 & 0x38)
                         | ((mem32_slice & 0x18) << 3) |
                            (mem32_slice & 0x7);
	checkResult (mem32_after == mem32_new,
		     "Test of vector register slice writing failed.");

	dut->eval ();

	mem32       = (int) mem32_read ();
	mem32_slice = (int) mem32_slice_read ();
	logRegHex (dut->clk, "read  mem32 [7:0]    ", 8, mem32," (after clk)");
	logRegHex (dut->clk, "read  mem32 [7:6,2:0]", 5, mem32_slice,
		   " (after clk)");

	// We have already tested that array element writing works, so we just
	// check that dhe slice of "mem32" after the clock is the
	// concatenation of the top 2 and bottom 3 bits of "mem32"
	checkResult (mem32_slice == (((mem32 & 0xc0) >> 3) | (mem32 & 0x07)),
		     "Test of array element slice writing failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Check we can read complex registers
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of complex register reading" << endl;
    cout << "================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;

	b       = (int) b_read ();
	mem32   = (int) mem32_read ();
	e       = (int) e_read ();
	int  l1 = (int) l1_read ();
	logRegHex (dut->clk, "read b    ",  8, b,     " (before clk)");
	logRegHex (dut->clk, "read mem32",  8, mem32, " (before clk)");
	logRegHex (dut->clk, "read e    ",  8, e,     " (before clk)");
	logRegHex (dut->clk, "read l1   ", 15, l1,    " (before clk)");

	dut->eval ();

	b     = (int) b_read ();
	mem32 = (int) mem32_read ();
	e     = (int) e_read ();
	l1    = (int) l1_read ();
	logRegHex (dut->clk, "read b    ",  8, b,     " (after clk)");
	logRegHex (dut->clk, "read mem32",  8, mem32, " (after clk)");
	logRegHex (dut->clk, "read e    ",  8, e,     " (after clk)");
	logRegHex (dut->clk, "read l1   ", 15, l1,    " (after clk)");

	// We have already tested that reading of registers, memory elements
	// and wires works. So we just need to check that l1 reads back as the
	// correct combination of bits after the clock. It should be the 15
	// bits: {b[3:0],mem[32][7:6],e[6:1],mem[32][2:0]}.
	checkResult (l1 == (  (((b     & 0x0f) >> 0) << 11)
			    | (((mem32 & 0xc0) >> 6) <<  9)
			    | (((e     & 0x7e) >> 1) <<  3)
			    | (((mem32 & 0x07) >> 0) <<  0)),
		     "Test of complex register reading l1 failed.");
    }

#ifdef TEST_VERBOSE
	cout << endl;
#endif

    checkFinish ("t_dpi_accessors unexpected finish");

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;

	e = 0x05 | (i << 4);
	f = 0xa0 | i;
	e_write ((const svBitVecVal *) &e);
	f_write ((const svBitVecVal *) &f);

	e       = (int) e_read ();
	f       = (int) f_read ();
	int  l2 = (int) l2_read ();
	logRegHex (dut->clk, "read e ", 8, e,  " (before clk)");
	logRegHex (dut->clk, "read f ", 8, f,  " (before clk)");
	logRegHex (dut->clk, "read l2", 8, l2, " (before clk)");

	dut->eval ();

	e       = (int) e_read ();
	f       = (int) f_read ();
	l2      = (int) l2_read ();
	logRegHex (dut->clk, "read e ", 8, e,  " (before clk)");
	logRegHex (dut->clk, "read f ", 8, f,  " (before clk)");
	logRegHex (dut->clk, "read l2", 8, l2, " (before clk)");

	// We have already tested that reading of registers, memory elements
	// and wires works. So we just need to check that l1 reads back as the
	// correct combination of bits after the clock. It should be the 8
	// bits: {e[7:4], f[3:0]}.
	checkResult (l2 == ((e & 0xf0) | (f & 0x0f)),
		     "Test of complex register reading l2 failed.");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Test we can write a complex register
#ifdef TEST_VERBOSE
    cout << endl;
    cout << "Test of complex register writing" << endl;
    cout << "================================" << endl;
#endif

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;

	b     = (int) b_read ();
	mem32 = (int) mem32_read ();
	e     = (int) e_read ();
	logRegHex (dut->clk, "read  b    ",  8, b,     " (before write)");
	logRegHex (dut->clk, "read  mem32",  8, mem32, " (before write)");
	logRegHex (dut->clk, "read  e    ",  8, e,     " (before write)");

	int  l1 = 0x5a5a;
	l1_write ((const svBitVecVal *) &l1);
	logRegHex (dut->clk, "write l1   ", 15, l1, " (before clk)");

	int  b_after     = (int) b_read ();
	int  mem32_after = (int) mem32_read ();
	int  e_after     = (int) e_read ();
	int  l1_after    = (int) l1_read ();
	logRegHex (dut->clk, "read  b    ",  8, b_after,     " (before clk)");
	logRegHex (dut->clk, "read  mem32",  8, mem32_after, " (before clk)");
	logRegHex (dut->clk, "read  e    ",  8, e_after,     " (before clk)");
	logRegHex (dut->clk, "read  l1   ", 15, l1_after,    " (before clk)");

	// We need to check that when we write l1, the correct fields, and
	// only the correct fields are set in its component registers, wires
	// and memory elements. l1 is 15 bits:
	// {b[3:0],mem[32][7:6],e[6:1],mem[32][2:0]}.
	int  b_new     = (b     & 0xf0) | ((l1 & 0x7800) >> 11);
	int  mem32_new = (mem32 & 0x38) | ((l1 & 0x0600) >> 3) | (l1 & 0x0007);
	int  e_new     = (e     & 0x81) | ((l1 & 0x01f8) >> 2);
	checkResult (   (b_new     == b_after)
		     && (mem32_new == mem32_after)
		     && (e_new     == e_after),
		     "Test of complex register writing l1 failed.");

	dut->eval ();

	b     = (int) b_read ();
	mem32 = (int) mem32_read ();
	d     = (int) d_read ();
	l1    = (int) l1_read ();
	logRegHex (dut->clk, "read  b    ",  8, b,     " (after clk)");
	logRegHex (dut->clk, "read  mem32",  8, mem32, " (after clk)");
	logRegHex (dut->clk, "read  d    ",  8, d,     " (after clk)");
	logRegHex (dut->clk, "read  l1   ", 15, l1,    " (after clk)");
    }

#ifdef TEST_VERBOSE
	cout << endl;
#endif

    checkFinish ("t_dpi_accessors unexpected finish");

    for (int i = 0; !Verilated::gotFinish () && (i < 4); i++) {
	dut->clk = 1 - dut->clk;

	e  = (int) e_read ();
	f  = (int) f_read ();
	logRegHex (dut->clk, "read  e ", 8, e,  " (before write)");
	logRegHex (dut->clk, "read  f ", 8, f,  " (before write)");

	int  l2 = 0xa5 + i;
	l2_write ((const svBitVecVal *) &l2);
	logRegHex (dut->clk, "write l2", 8, l2, " (before clk)");

	int  e_after  = (int) e_read ();
	int  f_after  = (int) f_read ();
	int  l2_after = (int) l2_read ();
	logRegHex (dut->clk, "read  e ", 8, e_after,  " (before clk)");
	logRegHex (dut->clk, "read  f ", 8, f_after,  " (before clk)");
	logRegHex (dut->clk, "read  l2", 8, l2_after, " (before clk)");

	// We need to check that when we write l2, the correct fields, and
	// only the correct fields are set in its component registers. l is 8
	// bits: {e[5:2], f[5:2]}
	int  e_new     = (e     & 0xc3) | ((l2 & 0xf0) >> 2);
	int  f_new     = (f     & 0xc3) | ((l2 & 0x0f) << 2);
	checkResult ((e_new == e_after) && (f_new == f_after),
		     "Test of complex register writing l2 failed.");

	dut->eval ();

	e  = (int) e_read ();
	f  = (int) f_read ();
	l2 = (int) l2_read ();
	logRegHex (dut->clk, "read  e ", 8, e,  " (before clk)");
	logRegHex (dut->clk, "read  f ", 8, f,  " (before clk)");
	logRegHex (dut->clk, "read  l2", 8, l2, " (before clk)");
    }

    checkFinish ("t_dpi_accessors unexpected finish");

    // Tidy up
    dut->final ();
    cout << "*-* All Finished *-*" << endl;;

}	// main ()

// Local Variables:
// c-file-style:"cc-mode"
// End:
