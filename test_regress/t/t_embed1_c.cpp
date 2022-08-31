// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2011-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "../t_embed1_child/Vt_embed1_child.h"
#include "svdpi.h"

#include <cstdio>

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_embed1__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

#include "verilated.h"

#ifdef NEED_EXTERNS
extern "C" {
extern void t_embed_child_initial();
extern void t_embed_child_final();
extern void t_embed_child_eval();
extern void t_embed_child_io_eval();  // TODO real function params here
}
#endif

//======================================================================

extern int T_Embed_Child_Unique;
int T_Embed_Child_Unique = 0;  // Address used for uniqueness

Vt_embed1_child* __get_modelp() {
    svScope scope = svGetScope();
    if (!scope) {
        vl_fatal(__FILE__, __LINE__, __FILE__, "svGetScope failed");
        return nullptr;
    }

    void* __modelp = svGetUserData(scope, &T_Embed_Child_Unique);
    if (!__modelp) {
        // Create the model
        const char* scopenamep = svGetNameFromScope(scope);
        if (!scopenamep) vl_fatal(__FILE__, __LINE__, __FILE__, "svGetNameFromScope failed");
        __modelp = new Vt_embed1_child{scopenamep};
        if (svPutUserData(scope, &T_Embed_Child_Unique, __modelp)) {
            vl_fatal(__FILE__, __LINE__, __FILE__, "svPutUserData failed");
        }
    }
    return reinterpret_cast<Vt_embed1_child*>(__modelp);
}

void __delete_modelp() {
    svScope scope = svGetScope();
    if (!scope) {
        vl_fatal(__FILE__, __LINE__, __FILE__, "svGetScope failed");
        return;
    }
    void* __modelp = svGetUserData(scope, &T_Embed_Child_Unique);
    if (__modelp) {
        delete reinterpret_cast<Vt_embed1_child*>(__modelp);
        __modelp = nullptr;
        if (svPutUserData(scope, &T_Embed_Child_Unique, __modelp)) {
            vl_fatal(__FILE__, __LINE__, __FILE__, "svPutUserData failed");
        }
    }
}

void t_embed_child_initial() {
    VL_DEBUG_IF(VL_PRINTF("    t_embed1_child_initial\n"););
    Vt_embed1_child* __modelp = __get_modelp();
    __modelp->eval();
}

void t_embed_child_final() {
    VL_DEBUG_IF(VL_PRINTF("    t_embed1_child_final\n"););
    Vt_embed1_child* __modelp = __get_modelp();
    __modelp->final();
    __delete_modelp();
}

void t_embed_child_eval() {
    VL_DEBUG_IF(VL_PRINTF("    t_embed1_child_eval\n"););
    Vt_embed1_child* __modelp = __get_modelp();
    __modelp->eval();
}

void t_embed_child_io_eval(unsigned char clk, unsigned char bit_in, const svBitVecVal* vec_in,
                           const svBitVecVal* wide_in, unsigned char is_ref,
                           unsigned char* bit_out, svBitVecVal* vec_out, svBitVecVal* wide_out,
                           unsigned char* did_init_out) {
    VL_DEBUG_IF(VL_PRINTF("    t_embed1_child_io_eval\n"););
    Vt_embed1_child* __modelp = __get_modelp();
    VL_DEBUG_IF(VL_PRINTF("[%0ld]      in clk=%x b=%x V=%x R=%x\n",  //
                          (long int)(VL_TIME_Q()), clk, bit_in, vec_in[0], is_ref););
    __modelp->clk = clk;
    __modelp->bit_in = bit_in;
    __modelp->vec_in = vec_in[0];
    __modelp->wide_in[0] = wide_in[0];
    __modelp->wide_in[1] = wide_in[1];
    __modelp->wide_in[2] = wide_in[2];
    __modelp->wide_in[3] = wide_in[3];
    __modelp->is_ref = is_ref;
    //
    __modelp->eval();
    // TODO maybe we should look at a "change detect" to know if we need to copy
    // out the variables; can return this value to the caller verilog code too
    //
    *bit_out = __modelp->bit_out;
    vec_out[0] = __modelp->vec_out;
    wide_out[0] = __modelp->wide_out[0];
    wide_out[1] = __modelp->wide_out[1];
    wide_out[2] = __modelp->wide_out[2];
    wide_out[3] = __modelp->wide_out[3];
    *did_init_out = __modelp->did_init_out;
    VL_DEBUG_IF(VL_PRINTF("[%0ld] out b=%x V=%x DI=%x\n",  //
                          (long int)(VL_TIME_Q()), *bit_out, *vec_out, *did_init_out););
}
