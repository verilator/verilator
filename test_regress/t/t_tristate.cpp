// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks

#include "Vt_tristate.h"

Vt_tristate *tb = NULL;

double sc_time_stamp() {
    return 0;
}

bool check() {
    bool pass;
    int c = (tb->A >> tb->SEL) & 0x1;

    if(tb->Z == c && tb->Y == c && tb->X == c && tb->W == c) {
	pass = true;
	printf("PASS: ");
    } else {
	pass = false;
	printf("FAIL: ");
    }
    printf("SEL=%d A=%d W=%d X=%d Y=%d Z=%d\n", tb->SEL, tb->A, tb->W, tb->X, tb->Y, tb->Z);
    return pass;
}

int main() {
    bool pass = true;
    tb = new Vt_tristate("tb");

    // loop through every possibility and check the result
    for (tb->SEL=0; tb->SEL<2; tb->SEL++) {
	for (tb->A=0; tb->A<4; tb->A++) {
	    tb->eval();
	    if(!check()) {
		pass =false;
	    }
	}
    }

    if(pass) {
	cout << "*-* All Finished *-*" << endl;
	tb->final();
    } else {
	vl_fatal(__FILE__,__LINE__,"top", "Unexpected results from tristate test\n");
    }
    return 0;
}
