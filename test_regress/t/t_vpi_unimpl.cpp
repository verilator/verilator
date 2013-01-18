// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "Vt_vpi_unimpl.h"
#include "verilated.h"
#include "svdpi.h"

#include "Vt_vpi_unimpl__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vpi.cpp"
#include "verilated_vcd_c.h"

#include <iostream>

// __FILE__ is too long
#define FILENM "t_vpi_unimpl.cpp"

#define DEBUG if (0) printf

unsigned int main_time = false;
unsigned int callback_count = false;

//======================================================================


class VlVpiHandle {
    /// For testing, etc, wrap vpiHandle in an auto-releasing class
    vpiHandle m_handle;
public:
    VlVpiHandle() : m_handle(NULL) { }
    VlVpiHandle(vpiHandle h) : m_handle(h) { }
    ~VlVpiHandle() { if (m_handle) { vpi_release_handle(m_handle); m_handle=NULL; } }
    operator vpiHandle () const { return m_handle; }
    inline VlVpiHandle& operator= (vpiHandle h) { m_handle = h; return *this; }
};

//======================================================================

#define CHECK_RESULT_VH(got, exp) \
    if ((got) != (exp)) { \
	printf("%%Error: %s:%d: GOT = %p   EXP = %p\n", \
	       FILENM,__LINE__, (got), (exp)); \
	return __LINE__; \
    }

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
	printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", FILENM,__LINE__); \
	return __LINE__; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got != exp)) { \
	cout<<dec<<"%Error: "<<FILENM<<":"<<__LINE__ \
	   <<": GOT = "<<(got)<<"   EXP = "<<(exp)<<endl;	\
	return __LINE__; \
    }

#define CHECK_RESULT_HEX(got, exp) \
    if ((got != exp)) { \
	cout<<dec<<"%Error: "<<FILENM<<":"<<__LINE__<<hex \
	   <<": GOT = "<<(got)<<"   EXP = "<<(exp)<<endl;	\
	return __LINE__; \
    }

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got),(exp))) { \
	printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", \
	       FILENM,__LINE__, (got)?(got):"<null>", (exp)?(exp):"<null>"); \
	return __LINE__; \
    }

#define CHECK_RESULT_CSTR_STRIP(got, exp) \
    CHECK_RESULT_CSTR(got+strspn(got, " "), exp)

int _mon_check_unimpl(p_cb_data cb_data) {
    static VlVpiHandle cb, clk_h;
    if (cb_data) {
	// this is the callback
        s_vpi_error_info info;
        vpi_chk_error(&info);
	callback_count++;
        printf("%%Info: got pli message %s\n", info.message);
    } else {
	// setup and install
	static t_cb_data cb_data;
        clk_h = vpi_handle_by_name((PLI_BYTE8*)"t.clk", NULL);

        cb_data.reason = cbPLIError;
        cb_data.cb_rtn = _mon_check_unimpl; // this function

        cb = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(cb);

        // now exercise unimplemented fns
	vpi_get_cb_info(cb, NULL);
        CHECK_RESULT(callback_count, 1);
	vpi_register_systf(NULL);
        CHECK_RESULT(callback_count, 2);
	vpi_get_systf_info(NULL, NULL);
        CHECK_RESULT(callback_count, 3);
        vpi_handle_multi(0, NULL, NULL);
        CHECK_RESULT(callback_count, 4);
        vpi_get64(0, NULL);
        CHECK_RESULT(callback_count, 5);
        vpi_get_delays(NULL, NULL);
        CHECK_RESULT(callback_count, 6);
        vpi_put_delays(NULL, NULL);
        CHECK_RESULT(callback_count, 7);
	vpi_get_value_array(NULL, NULL, NULL, 0);
        CHECK_RESULT(callback_count, 8);
	vpi_put_value_array(NULL, NULL, NULL, 0);
        CHECK_RESULT(callback_count, 9);
	vpi_get_time(NULL, NULL);
        CHECK_RESULT(callback_count, 10);
	vpi_mcd_name(0);
        CHECK_RESULT(callback_count, 11);
        vpi_compare_objects(NULL, NULL);
        CHECK_RESULT(callback_count, 12);
	vpi_get_data(0, NULL, 0);
        CHECK_RESULT(callback_count, 13);
	vpi_put_data(0, NULL, 0);
        CHECK_RESULT(callback_count, 14);
	vpi_get_userdata(NULL);
        CHECK_RESULT(callback_count, 15);
	vpi_put_userdata(NULL, NULL);
        CHECK_RESULT(callback_count, 16);
        vpi_handle_by_multi_index(NULL, 0, NULL);
        CHECK_RESULT(callback_count, 17);
    }
    return 0; // Ok
}

int mon_check() {
    // Callback from initial block in monitor
    if (int status = _mon_check_unimpl(NULL)) return status;
    return 0; // Ok
}

//======================================================================


double sc_time_stamp () {
    return main_time;
}
int main(int argc, char **argv, char **env) {
    double sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);
    Verilated::fatalOnVpiError(0); // we're going to be checking for these errors do don't crash out

    VM_PREFIX* topp = new VM_PREFIX ("");  // Note null name - we're flattening it out

#ifdef VERILATOR
# ifdef TEST_VERBOSE
    Verilated::scopesDump();
# endif
#endif

    Verilated::traceEverOn(true);
    VerilatedVcdC* tfp = new VerilatedVcdC;
#if VM_TRACE
    VL_PRINTF("Enabling waves...\n");
    topp->trace (tfp, 99);
    tfp->open ("obj_dir/t_vpi_var/simx.vcd");
#endif

    topp->eval();
    topp->clk = 0;
    main_time += 10;

    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
	main_time += 1;
	topp->eval();
	VerilatedVpi::callValueCbs();
	topp->clk = !topp->clk;
	//mon_do();
#if VM_TRACE
	if (tfp) tfp->dump (main_time);
#endif
    }
    CHECK_RESULT(callback_count, 17);
    if (!Verilated::gotFinish()) {
	vl_fatal(FILENM,__LINE__,"main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    delete topp; topp=NULL;
    exit(0L);
}
