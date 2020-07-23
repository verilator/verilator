// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop.h"
#include "Vtop__Syms.h"

#include <functional>
#include <vector>
#include <set>

//==========


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


class Process
{
    public:
        std::vector <std::function<bool()>> run_conditions; // waits for arbitrary conditions
        std::vector <unsigned int> time_conditions; // waits for specific simulation times
        std::vector <std::function<void()>> eval_steps; // unbreakable steps to eval
        unsigned int current_step = 0; // index for iterating the steps vector
        bool repeatable = 0; // whether after finishing the last step we should go back to the first one
        bool finished = false; // whether it should or should not be invoked again
};


class Timer
{
    public:
        unsigned long simulation_time;

        std::set<unsigned long> requested_slots;

        void advance_time() {
            if (requested_slots.size() == 0) {
                VL_DBG_MSGF("+    No next time slot requested\n");
            }

            auto next_time = requested_slots.begin();
            simulation_time = *next_time;
            requested_slots.erase(next_time);

            VL_DBG_MSGF("+    Simulation time advanced to %lu\n", simulation_time);
        }

        unsigned int offset(unsigned int offset) {
            return simulation_time + offset;
        }
};

//==========
// Definition of various things needed for simulation
// Most of it should probably not be globals

// Define the simulation timer
Timer timer{};

// TODO define a vector of active processes

// Define the events
Event ready_to_finish{};

// Definition of various Processes and their steps

// FIRST
Process first{};

// Steps for first();
void first_0(Vtop__Syms* __restrict vlSymsp) {
    // Nothing until #300

    // step ends with #300 - add a condition for that
    // The value of 300 has to be read from the node (once it is included in th
    // AST) - hardcoding it for now.
    first.time_conditions.push_back(timer.offset(300));
}

void first_1(Vtop__Syms* __restrict vlSymsp) {
    // All we have to do is trigger the event
    ready_to_finish.trigger();

    // This is the last step and we are not expected to start from the
    // beginning (could be extracted to a separate step - e.g. first_final)
    first.finished = true;
}


//==========

VL_CTOR_IMP(Vtop) {
    Vtop__Syms* __restrict vlSymsp = __VlSymsp = new Vtop__Syms(this, name());
    Vtop* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void Vtop::__Vconfigure(Vtop__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

Vtop::~Vtop() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void Vtop::_initial__TOP__1(Vtop__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop::_initial__TOP__1\n"); );
    Vtop* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    VL_WRITEF("->ready_to_finish;\n");
    VL_WRITEF("@ready_to_finish;\n");
    VL_FINISH_MT("top.sv", 44, "");
    VL_WRITEF("Everything has been started!\n");
}

void Vtop::_eval_initial(Vtop__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop::_eval_initial\n"); );
    Vtop* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_initial__TOP__1(vlSymsp);
}

void Vtop::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop::final\n"); );
    // Variables
    Vtop__Syms* __restrict vlSymsp = this->__VlSymsp;
    Vtop* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vtop::_eval_settle(Vtop__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop::_eval_settle\n"); );
    Vtop* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void Vtop::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop::_ctor_var_reset\n"); );
}
