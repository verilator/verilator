// -*- C++ -*-
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

#include "Vt_vpi_var.h"
#include "verilated.h"
#include "svdpi.h"

#include "Vt_vpi_var__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vpi.cpp"
#include "verilated_vcd_c.h"

#include <iostream>

// __FILE__ is too long
#define FILENM "t_vpi_var.cpp"

unsigned int main_time = false;
unsigned int callback_count = false;
unsigned int callback_count_half = false;

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

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got),(exp))) { \
	printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", \
	       FILENM,__LINE__, (got)?(got):"<null>", (exp)?(exp):"<null>"); \
	return __LINE__; \
    }

int _mon_check_mcd() {
    PLI_INT32 status;
    
    PLI_UINT32 mcd;
    PLI_BYTE8* filename = (PLI_BYTE8*)"obj_dir/t_vpi_var/mcd_open.tmp";
    mcd = vpi_mcd_open(filename);
    CHECK_RESULT_NZ(mcd);

    {   // Check it got written
	FILE* fp = fopen(filename,"r");
	CHECK_RESULT_NZ(fp);
	fclose(fp);
    }

    status = vpi_mcd_printf(mcd, (PLI_BYTE8*)"hello %s", "vpi_mcd_printf");
    CHECK_RESULT(status, strlen("hello vpi_mcd_printf"));

    status = vpi_mcd_flush(mcd);
    CHECK_RESULT(status, 0);

    status = vpi_mcd_close(mcd);
    CHECK_RESULT(status, 0);

    status = vpi_flush();
    CHECK_RESULT(status, 0);

    return 0;
}

int _mon_check_callbacks() {
    t_cb_data cb_data;
    cb_data.reason = cbEndOfSimulation;
    cb_data.cb_rtn = NULL;
    cb_data.user_data = 0;

    vpiHandle vh = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh);

    PLI_INT32 status = vpi_remove_cb(vh);
    CHECK_RESULT_NZ(status);

    return 0;
}

int _value_callback(p_cb_data cb_data) {
  CHECK_RESULT(cb_data->value->value.integer+10, main_time);
  callback_count++;
  return 0;
}

int _value_callback_half(p_cb_data cb_data) {
  CHECK_RESULT(cb_data->value->value.integer*2+10, main_time);
  callback_count_half++;
  return 0;
}

int _mon_check_value_callbacks() {
    vpiHandle vh1 = vpi_handle_by_name((PLI_BYTE8*)"t.count", NULL);
    CHECK_RESULT_NZ(vh1);

    s_vpi_value v;
    v.format = vpiIntVal;
    vpi_get_value(vh1, &v);

    t_cb_data cb_data;
    cb_data.reason = cbValueChange;
    cb_data.cb_rtn = _value_callback;
    cb_data.obj = vh1;
    cb_data.value = &v;

    vpiHandle vh = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh);

    vh1 = vpi_handle_by_name((PLI_BYTE8*)"t.half_count", NULL);
    CHECK_RESULT_NZ(vh1);

    cb_data.obj = vh1;
    cb_data.cb_rtn = _value_callback_half;

    vh = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh);
    return 0;
}

int _mon_check_var() {
    VlVpiHandle vh1 = vpi_handle_by_name((PLI_BYTE8*)"t.onebit", NULL);
    CHECK_RESULT_NZ(vh1);

    VlVpiHandle vh2 = vpi_handle_by_name((PLI_BYTE8*)"t", NULL);
    CHECK_RESULT_NZ(vh2);

    // scope attributes
    const char* p;
    p = vpi_get_str(vpiName, vh2);
    CHECK_RESULT_CSTR(p, "t");
    p = vpi_get_str(vpiFullName, vh2);
    CHECK_RESULT_CSTR(p, "t");

    VlVpiHandle vh3 = vpi_handle_by_name((PLI_BYTE8*)"onebit", vh2);
    CHECK_RESULT_NZ(vh3);

    // onebit attributes
    PLI_INT32 d;
    d = vpi_get(vpiType, vh3);
    CHECK_RESULT(d, vpiReg);
    d = vpi_get(vpiDirection, vh3);
    CHECK_RESULT(d, vpiNoDirection);
    d = vpi_get(vpiVector, vh3);
    CHECK_RESULT(d, 0);

    p = vpi_get_str(vpiName, vh3);
    CHECK_RESULT_CSTR(p, "onebit");
    p = vpi_get_str(vpiFullName, vh3);
    CHECK_RESULT_CSTR(p, "t.onebit");

    // array attributes
    VlVpiHandle vh4 = vpi_handle_by_name((PLI_BYTE8*)"t.fourthreetwoone", NULL);
    CHECK_RESULT_NZ(vh4);
    d = vpi_get(vpiVector, vh4);
    CHECK_RESULT(d, 1);

    t_vpi_value tmpValue;
    tmpValue.format = vpiIntVal;
    {
	VlVpiHandle vh10 = vpi_handle(vpiLeftRange, vh4);
	CHECK_RESULT_NZ(vh10);
	vpi_get_value(vh10, &tmpValue);
	CHECK_RESULT(tmpValue.value.integer,2);
    }
    {
	VlVpiHandle vh10 = vpi_handle(vpiRightRange, vh4);
	CHECK_RESULT_NZ(vh10);
	vpi_get_value(vh10, &tmpValue);
	CHECK_RESULT(tmpValue.value.integer,1);
    }
    {
	VlVpiHandle vh10 = vpi_iterate(vpiMemoryWord, vh4);
	CHECK_RESULT_NZ(vh10);
	VlVpiHandle vh11 = vpi_scan(vh10);
	CHECK_RESULT_NZ(vh11);
	VlVpiHandle vh12 = vpi_handle(vpiLeftRange, vh11);
	CHECK_RESULT_NZ(vh12);
	vpi_get_value(vh12, &tmpValue);
	CHECK_RESULT(tmpValue.value.integer,4);
	VlVpiHandle vh13 = vpi_handle(vpiRightRange, vh11);
	CHECK_RESULT_NZ(vh13);
	vpi_get_value(vh13, &tmpValue);
	CHECK_RESULT(tmpValue.value.integer,3);
    }

    return 0;
}

int _mon_check_varlist() {
    const char* p;

    VlVpiHandle vh2 = vpi_handle_by_name((PLI_BYTE8*)"t.sub", NULL);
    CHECK_RESULT_NZ(vh2);

    VlVpiHandle vh10 = vpi_iterate(vpiReg, vh2);
    CHECK_RESULT_NZ(vh10);

    VlVpiHandle vh11 = vpi_scan(vh10);
    CHECK_RESULT_NZ(vh11);
    p = vpi_get_str(vpiFullName, vh11);
    CHECK_RESULT_CSTR(p, "t.sub.subsig1");

    VlVpiHandle vh12 = vpi_scan(vh10);
    CHECK_RESULT_NZ(vh12);
    p = vpi_get_str(vpiFullName, vh12);
    CHECK_RESULT_CSTR(p, "t.sub.subsig2");

    VlVpiHandle vh13 = vpi_scan(vh10);
    CHECK_RESULT(vh13,0);

    return 0;
}

int _mon_check_getput() {
    VlVpiHandle vh2 = vpi_handle_by_name((PLI_BYTE8*)"t.onebit", NULL);
    CHECK_RESULT_NZ(vh2);

    s_vpi_value v;
    v.format = vpiIntVal;
    vpi_get_value(vh2, &v);
    CHECK_RESULT(v.value.integer, 0);

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    v.value.integer = 1;
    vpi_put_value(vh2, &v, &t, vpiNoDelay);

    vpi_get_value(vh2, &v);
    CHECK_RESULT(v.value.integer, 1);

    return 0;
}

int _mon_check_quad() {
    VlVpiHandle vh2 = vpi_handle_by_name((PLI_BYTE8*)"t.quads", NULL);
    CHECK_RESULT_NZ(vh2);

    s_vpi_value v;
    t_vpi_vecval vv;  bzero(&vv,sizeof(vv));

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;

    VlVpiHandle vhidx2 = vpi_handle_by_index(vh2, 2);
    CHECK_RESULT_NZ(vhidx2);
    VlVpiHandle vhidx3 = vpi_handle_by_index(vh2, 3);
    CHECK_RESULT_NZ(vhidx2);

    v.format = vpiVectorVal;
    v.value.vector = &vv;
    v.value.vector[1].aval = 0x12819213UL;
    v.value.vector[0].aval = 0xabd31a1cUL;
    vpi_put_value(vhidx2, &v, &t, vpiNoDelay);

    v.format = vpiVectorVal;
    v.value.vector = &vv;
    v.value.vector[1].aval = 0x1c77bb9bUL;
    v.value.vector[0].aval = 0x3784ea09UL;
    vpi_put_value(vhidx3, &v, &t, vpiNoDelay);

    vpi_get_value(vhidx2, &v);
    CHECK_RESULT(v.value.vector[1].aval, 0x12819213UL);
    CHECK_RESULT(v.value.vector[1].bval, 0);

    vpi_get_value(vhidx3, &v);
    CHECK_RESULT(v.value.vector[1].aval, 0x1c77bb9bUL);
    CHECK_RESULT(v.value.vector[1].bval, 0);

    return 0;
}

int mon_check() {
    // Callback from initial block in monitor
    if (int status = _mon_check_mcd()) return status;
    if (int status = _mon_check_callbacks()) return status;
    if (int status = _mon_check_value_callbacks()) return status;
    if (int status = _mon_check_var()) return status;
    if (int status = _mon_check_varlist()) return status;
    if (int status = _mon_check_getput()) return status;
    if (int status = _mon_check_quad()) return status;
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
    CHECK_RESULT(callback_count, 501);
    CHECK_RESULT(callback_count_half, 250);
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
