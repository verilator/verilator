// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VTOP__SYMS_H_
#define _VTOP__SYMS_H_  // guard

#include "verilated_heavy.h"

// INCLUDE MODULE CLASSES
#include "Vtop.h"

class Event
{
    public:
        bool triggered = false;

        void trigger() {
            triggered = true;
        }

        void reset() {
            triggered = false;
        }
};

// SYMS CLASS
class Vtop__Syms : public VerilatedSyms {
  public:
    // XXX signals renamed to make the code more readable
    IData/*31:0*/ j;
    IData/*31:0*/ i;

    // XXX what type to use? (this is 'process job')
    void* job;

    Event ready_to_finish{};
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    Vtop*                          TOPp;
    
    // CREATORS
    Vtop__Syms(Vtop* topp, const char* namep);
    ~Vtop__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
