// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks

#ifdef T_COND
# include "Vt_tri_gate_cond.h"
#elif defined(T_BUFIF0)
# include "Vt_tri_gate_bufif0.h"
#elif defined(T_BUFIF1)
# include "Vt_tri_gate_bufif1.h"
#elif defined(T_NOTIF0)
# include "Vt_tri_gate_notif0.h"
#elif defined(T_NOTIF1)
# include "Vt_tri_gate_notif1.h"
#else
# error "Unknown test"
#endif

VM_PREFIX* tb = NULL;

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
#ifdef TEST_VERBOSE
    printf("SEL=%d A=%d W=%d X=%d Y=%d Z=%d\n", tb->SEL, tb->A, tb->W, tb->X, tb->Y, tb->Z);
#endif
    return pass;
}

int main() {
    bool pass = true;

    Verilated::debug(0);
    tb = new VM_PREFIX ("tb");

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
	VL_PRINTF("*-* All Finished *-*\n");
	tb->final();
    } else {
	vl_fatal(__FILE__,__LINE__,"top", "Unexpected results from tristate test\n");
    }
    return 0;
}
