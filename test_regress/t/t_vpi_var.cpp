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

#define TEST_MSG if (0) printf

unsigned int main_time = false;
unsigned int callback_count = false;
unsigned int callback_count_half = false;
unsigned int callback_count_quad = false;
unsigned int callback_count_strs = false;
unsigned int callback_count_strs_max = 500;

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
    if ((got) != (exp)) {			     \
	cout<<dec<<"%Error: "<<FILENM<<":"<<__LINE__ \
	   <<": GOT = "<<(got)<<"   EXP = "<<(exp)<<endl;	\
	return __LINE__; \
    }

#define CHECK_RESULT_HEX(got, exp) \
    if ((got) != (exp)) {				  \
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

int _value_callback_quad(p_cb_data cb_data) {
    for (int index=0;index<2;index++) {
	CHECK_RESULT_HEX(cb_data->value->value.vector[1].aval, (unsigned long)((index==2)?0x1c77bb9bUL:0x12819213UL));
	CHECK_RESULT_HEX(cb_data->value->value.vector[0].aval, (unsigned long)((index==2)?0x3784ea09UL:0xabd31a1cUL));
    }
    callback_count_quad++;
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

    vh1 = vpi_handle_by_name((PLI_BYTE8*)"t.quads", NULL);
    CHECK_RESULT_NZ(vh1);

    v.format = vpiVectorVal;
    cb_data.obj = vh1;
    cb_data.cb_rtn = _value_callback_quad;

    vh = vpi_register_cb(&cb_data);
    CHECK_RESULT_NZ(vh);

    vh1 = vpi_handle_by_index(vh1, 2);
    CHECK_RESULT_NZ(vh1);

    cb_data.obj = vh1;
    cb_data.cb_rtn = _value_callback_quad;

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
    t_vpi_vecval vv[2];  bzero(&vv,sizeof(vv));

    s_vpi_time t;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;

    VlVpiHandle vhidx2 = vpi_handle_by_index(vh2, 2);
    CHECK_RESULT_NZ(vhidx2);
    VlVpiHandle vhidx3 = vpi_handle_by_index(vh2, 3);
    CHECK_RESULT_NZ(vhidx2);

    v.format = vpiVectorVal;
    v.value.vector = vv;
    v.value.vector[1].aval = 0x12819213UL;
    v.value.vector[0].aval = 0xabd31a1cUL;
    vpi_put_value(vhidx2, &v, &t, vpiNoDelay);

    v.format = vpiVectorVal;
    v.value.vector = vv;
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

int _mon_check_string() {
    static struct {
	const char *name;
        const char *initial;
        const char *value;
    } text_test_obs[] = {
        {"t.text_byte", "B", "xxA"}, // x's dropped
        {"t.text_half", "Hf", "xxT2"}, // x's dropped
        {"t.text_word", "Word", "Tree"},
        {"t.text_long", "Long64b", "44Four44"},
        {"t.text"     , "Verilog Test module", "lorem ipsum"},
    };

    for (int i=0; i<5; i++) {
      VlVpiHandle vh1 = vpi_handle_by_name((PLI_BYTE8*)text_test_obs[i].name, NULL);
      CHECK_RESULT_NZ(vh1);

      s_vpi_value v;
      s_vpi_time t = { vpiSimTime, 0, 0};
      s_vpi_error_info e;

      v.format = vpiStringVal;
      vpi_get_value(vh1, &v);
      if (vpi_chk_error(&e)) {
	  printf("%%vpi_chk_error : %s\n", e.message);
      }

      CHECK_RESULT_CSTR_STRIP(v.value.str, text_test_obs[i].initial);

      v.value.str = (PLI_BYTE8*)text_test_obs[i].value;
      vpi_put_value(vh1, &v, &t, vpiNoDelay);
    }

    return 0;
}

int _mon_check_putget_str(p_cb_data cb_data) {
    static VlVpiHandle cb;
    static struct {
	VlVpiHandle scope, sig, rfr, check, verbose;
        char str[128+1];          // char per bit plus null terminator
        int type;                 // value type in .str
        union {
          PLI_INT32    integer;
          s_vpi_vecval vector[4];
	} value;                 // reference
    } data[129];
    if (cb_data) {
	// this is the callback
        static unsigned int seed = 1;
        s_vpi_time t;
        t.type = vpiSimTime;
        t.high = 0;
        t.low = 0;
        for (int i=2; i<=128; i++) {
	  static s_vpi_value v;
          int words = (i+31)>>5;
	  TEST_MSG("========== %d ==========\n", i);
          if (callback_count_strs) {
	      // check persistance
              if (data[i].type) {
                  v.format = data[i].type;
	      } else {
		  static PLI_INT32 vals[] = {vpiBinStrVal, vpiOctStrVal, vpiHexStrVal, vpiDecStrVal};
                  v.format = vals[rand_r(&seed) % ((words>2)?3:4)];
		  TEST_MSG("new format %d\n", v.format);
	      }
              vpi_get_value(data[i].sig, &v);
	      TEST_MSG("%s\n", v.value.str);
              if (data[i].type) {
                  CHECK_RESULT_CSTR(v.value.str, data[i].str);
	      } else {
                  data[i].type = v.format;
                  strcpy(data[i].str, v.value.str);
	      }
	  }

          // check for corruption
          v.format = (words==1)?vpiIntVal:vpiVectorVal;
          vpi_get_value(data[i].sig, &v);
          if (v.format == vpiIntVal) {
              TEST_MSG("%08x %08x\n", v.value.integer, data[i].value.integer);
              CHECK_RESULT(v.value.integer, data[i].value.integer);
	  } else {
              for (int k=0; k < words; k++) {
	          TEST_MSG("%d %08x %08x\n", k, v.value.vector[k].aval, data[i].value.vector[k].aval);
                  CHECK_RESULT_HEX(v.value.vector[k].aval, data[i].value.vector[k].aval);
	      }
	  }

          if (callback_count_strs & 7) {
              // put same value back - checking encoding/decoding equivalent
              v.format = data[i].type;
              v.value.str = data[i].str;
              vpi_put_value(data[i].sig, &v, &t, vpiNoDelay);
              v.format = vpiIntVal;
              v.value.integer = 1;
              //vpi_put_value(data[i].verbose, &v, &t, vpiNoDelay);
              vpi_put_value(data[i].check, &v, &t, vpiNoDelay);
	  } else {
              // stick a new random value in
              unsigned int mask = ((i&31)?(1<<(i&31)):0)-1;
              if (words == 1) {
                  v.value.integer = rand_r(&seed);
                  data[i].value.integer = v.value.integer &= mask;
                  v.format = vpiIntVal;
	          TEST_MSG("new value %08x\n", data[i].value.integer);
	      } else {
	          TEST_MSG("new value\n");
	          for (int j=0; j<4; j++) {
                      data[i].value.vector[j].aval = rand_r(&seed);
                      if (j==(words-1)) {
			  data[i].value.vector[j].aval &= mask;
		      }
	              TEST_MSG(" %08x\n", data[i].value.vector[j].aval);
	          }
                  v.value.vector = data[i].value.vector;
                  v.format = vpiVectorVal;
	      }
              vpi_put_value(data[i].sig, &v, &t, vpiNoDelay);
              vpi_put_value(data[i].rfr, &v, &t, vpiNoDelay);
	  }
          if ((callback_count_strs & 1) == 0) data[i].type = 0;
	}
        if (++callback_count_strs == callback_count_strs_max) {
          int success = vpi_remove_cb(cb);
          CHECK_RESULT_NZ(success);
	};
    } else {
	// setup and install
        for (int i=1; i<=128; i++) {
            char buf[32];
            snprintf(buf, sizeof(buf), "t.arr[%d].arr", i);
	    CHECK_RESULT_NZ(data[i].scope   = vpi_handle_by_name((PLI_BYTE8*)buf, NULL));
	    CHECK_RESULT_NZ(data[i].sig     = vpi_handle_by_name((PLI_BYTE8*)"sig", data[i].scope));
	    CHECK_RESULT_NZ(data[i].rfr     = vpi_handle_by_name((PLI_BYTE8*)"rfr", data[i].scope));
	    CHECK_RESULT_NZ(data[i].check   = vpi_handle_by_name((PLI_BYTE8*)"check", data[i].scope));
	    CHECK_RESULT_NZ(data[i].verbose = vpi_handle_by_name((PLI_BYTE8*)"verbose", data[i].scope));
	}

	static t_cb_data cb_data;
	static s_vpi_value v;
        static VlVpiHandle count_h = vpi_handle_by_name((PLI_BYTE8*)"t.count", NULL);

        cb_data.reason = cbValueChange;
        cb_data.cb_rtn = _mon_check_putget_str; // this function
        cb_data.obj = count_h;
        cb_data.value = &v;
        v.format = vpiIntVal;

        cb = vpi_register_cb(&cb_data);
        CHECK_RESULT_NZ(cb);
    }
    return 0;
}

int _mon_check_vlog_info() {
    s_vpi_vlog_info vlog_info;
    PLI_INT32 rtn = vpi_get_vlog_info(&vlog_info);
    CHECK_RESULT(rtn, 1);
    CHECK_RESULT(vlog_info.argc, 4);
    CHECK_RESULT_CSTR(vlog_info.argv[1], "+PLUS");
    CHECK_RESULT_CSTR(vlog_info.argv[2], "+INT=1234");
    CHECK_RESULT_CSTR(vlog_info.argv[3], "+STRSTR");
    CHECK_RESULT_CSTR(vlog_info.product, "Verilator");
    CHECK_RESULT(strlen(vlog_info.version) > 0, 1);

    return 0;
}

#define CHECK_ENUM_STR(fn, enum) \
    do { \
        const char* strVal = VerilatedVpiError::fn(enum); \
        CHECK_RESULT_CSTR(strVal, #enum); \
    } while (0)

int _mon_check_vl_str() {

    CHECK_ENUM_STR(strFromVpiVal, vpiBinStrVal);
    CHECK_ENUM_STR(strFromVpiVal, vpiRawFourStateVal);

    CHECK_ENUM_STR(strFromVpiObjType, vpiAlways);
    CHECK_ENUM_STR(strFromVpiObjType, vpiWhile);
    CHECK_ENUM_STR(strFromVpiObjType, vpiAttribute);
    CHECK_ENUM_STR(strFromVpiObjType, vpiUdpArray);
    CHECK_ENUM_STR(strFromVpiObjType, vpiContAssignBit);
    CHECK_ENUM_STR(strFromVpiObjType, vpiGenVar);

    CHECK_ENUM_STR(strFromVpiMethod, vpiCondition);
    CHECK_ENUM_STR(strFromVpiMethod, vpiStmt);

    CHECK_ENUM_STR(strFromVpiCallbackReason, cbValueChange);
    CHECK_ENUM_STR(strFromVpiCallbackReason, cbAtEndOfSimTime);

    CHECK_ENUM_STR(strFromVpiProp, vpiType);
    CHECK_ENUM_STR(strFromVpiProp, vpiProtected);
    CHECK_ENUM_STR(strFromVpiProp, vpiDirection);
    CHECK_ENUM_STR(strFromVpiProp, vpiTermIndex);
    CHECK_ENUM_STR(strFromVpiProp, vpiConstType);
    CHECK_ENUM_STR(strFromVpiProp, vpiAutomatic);
    CHECK_ENUM_STR(strFromVpiProp, vpiOffset);
    CHECK_ENUM_STR(strFromVpiProp, vpiStop);
    CHECK_ENUM_STR(strFromVpiProp, vpiIsProtected);

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
    if (int status = _mon_check_string()) return status;
    if (int status = _mon_check_putget_str(NULL)) return status;
    if (int status = _mon_check_vlog_info()) return status;
    if (int status = _mon_check_vl_str()) return status;
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
    CHECK_RESULT(callback_count_quad, 2);
    CHECK_RESULT(callback_count_strs, callback_count_strs_max);
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
