// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks

#include "Vt_tri_pullup.h"

Vt_tri_pullup *tb = NULL;

double sc_time_stamp() {
    return 0;
}

bool check() {
    bool pass;
    int Z, Y, X;
    if (tb->OE) {
	Z = tb->A;
	Y = tb->A;
	X = tb->A;
    } else {
	Z = 1;
	Y = 0;
	X = 1;
    }

    if (tb->Z == Z  &&  tb->Y == Y  && tb->X == X) {
	printf("PASS: ");
	pass = true;
    } else {
	printf("FAIL: ");
	pass = false;
    }
#ifdef TEST_VERBOSE
    printf("OE=%d A=%d X=%d Y=%d Z=%d\n", tb->OE, tb->A, tb->X, tb->Y, tb->Z);
#endif
    return pass;
}

int main() {
    bool pass = true;

    Verilated::debug(0);
    tb  = new Vt_tri_pullup("tb");

    // loop through every possibility and check the result
    for (tb->OE=0; tb->OE<2; tb->OE++) {
	for (tb->A=0; tb->A<2; tb->A++) {
	    tb->eval();
	    if (!check()) {
		pass = false;
	    }
	}
    }

    if (pass) {
	VL_PRINTF("*-* All Finished *-*\n");
	tb->final();
    } else {
	vl_fatal(__FILE__,__LINE__,"top", "Unexpected results from pullup test\n");
    }
    return 0;
}
