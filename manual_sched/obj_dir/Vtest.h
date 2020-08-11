// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VTEST_H_
#define _VTEST_H_  // guard

#include "verilated_heavy.h"

//==========

class Vtest__Syms;

//----------

VL_MODULE(Vtest) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clk,0,0);
    VL_IN8(clk1,0,0);
    VL_OUT8(a,0,0);
    VL_IN8(b,0,0);
    VL_OUT8(c,0,0);
    VL_OUT8(d,0,0);
    VL_OUT8(e,0,0);
    VL_IN8(f,0,0);
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk1;
    CData/*0:0*/ __Vclklast__TOP__clk;
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    Vtest__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(Vtest);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    Vtest(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~Vtest();
    
    // API METHODS
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    
    // INTERNAL METHODS
  private:
    static void _eval_initial_loop(Vtest__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(Vtest__Syms* symsp, bool first);
  private:
    static QData _change_request(Vtest__Syms* __restrict vlSymsp);
    static QData _change_request_1(Vtest__Syms* __restrict vlSymsp);
  public:
    static void _combo__TOP__2(Vtest__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(Vtest__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(Vtest__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_re_initial(Vtest__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(Vtest__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _initial__TOP__1(Vtest__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _initial__TOP__1_REACTIVE(Vtest__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__4(Vtest__Syms* __restrict vlSymsp);
    static void _sequent__TOP__4_NBA(Vtest__Syms* __restrict vlSymsp);
    static void _sequent__TOP__5(Vtest__Syms* __restrict vlSymsp);
    static void _sequent__TOP__5_NBA(Vtest__Syms* __restrict vlSymsp);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
