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
        std::vector <std::function<bool(Vtop__Syms* __restrict vlSymsp)>> run_conditions; // waits for arbitrary conditions
        std::vector <unsigned int> time_conditions; // waits for specific simulation times
        std::vector <std::function<void()>> eval_steps; // unbreakable steps to eval
        unsigned int current_step = 0; // index for iterating the steps vector
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

// Define the events
Event e_ready_to_finish{};

// Define a vector of active processes
std::vector <Process> active_processes;

// Definition of various Processes (including unnamed subprocesses)
Process initial{};
    Process p_first{};
    Process p_second{};
        Process p_second_0{}; // These come from the fork in second()
        Process p_second_1{};
        Process p_second_2{};
            Process p_second_2_0{}; // This is unfurtunate
    Process p_initial_0{};

// INITIAL

void s_initial_0(Vtop__Syms* __restrict vlSymsp) {
    // Activate all the processes under fork
    active_processes.push_back(p_first);
    active_processes.push_back(p_second);
    active_processes.push_back(p_initial_0);

    // fork ends with 'join_any' so we continue in the same step
    VL_WRITEF("Everything has been started!\n");
}


// FIRST

void s_first_0(Vtop__Syms* __restrict vlSymsp) {
    // Nothing until #300

    // step ends with #300 - add a condition for that
    // The value of 300 has to be read from the node (once it is included in th
    // AST) - hardcoding it for now.
    p_first.time_conditions.push_back(timer.offset(300));
}

void s_first_1(Vtop__Syms* __restrict vlSymsp) {
    // All we have to do is trigger the event
    e_ready_to_finish.trigger();

    // This is the last step and we are not expected to start from the
    // beginning (could be extracted to a separate step - e.g. first_final)
    p_first.finished = true;
}

// SECOND

void s_second_0(Vtop__Syms* __restrict vlSymsp) {
    // forks to three unnamed blocks
    active_processes.push_back(p_second_0);
    active_processes.push_back(p_second_1);
    active_processes.push_back(p_second_2);

    // fork_any - wait until any of the forked processes finishes
    p_second.run_conditions.push_back([](Vtop__Syms* __restrict vlSymsp) {
                return p_second_0.finished || p_second_1.finished || p_second_2.finished;
            });
}

void s_second_0_0(Vtop__Syms* __restrict vlSymsp) {
    // Regular i = 5
    p_second_0.finished = true;
}

void s_second_1_0(Vtop__Syms* __restrict vlSymsp) {
    // #10;
    p_second_1.time_conditions.push_back(timer.offset(10));
}

void s_second_1_1(Vtop__Syms* __restrict vlSymsp) {
    // job = process::self();

    // XXX find the job variable and attach something meaningful to it
    p_second_1.finished = true;
}

void s_second_2_0(Vtop__Syms* __restrict vlSymsp) {
    // while (j < 10) begin
    //         #5;
    //         j++;
    // end

    // This is unfortunate, as there is no clean way to
    // handle loops with the proposed approach.
    // One way is to represent loop as a separate "Process"
    // which is done here

    active_processes.push_back(p_second_2_0);

    p_second_2.run_conditions.push_back([](Vtop__Syms* __restrict vlSymsp) {
                return p_second_2_0.finished;
            });
}

void s_second_2_0_0(Vtop__Syms* __restrict vlSymsp) {
    // #5
    p_first.time_conditions.push_back(timer.offset(5));
}

void s_second_2_0_1(Vtop__Syms* __restrict vlSymsp) {
    // j++;
    // XXX extract j from symbols and do j++

    if (true /* XXX j >= 10 */) {
        p_second_2_0.finished = true;
    }
}

void s_second_1(Vtop__Syms* __restrict vlSymsp) {
    VL_WRITEF("TODO: $display After fork: (...)\n");

    // wait (j == 3)
    p_second.run_conditions.push_back([](Vtop__Syms* __restrict vlSymsp) {
                // TODO FIXME extract j from Vtop__Syms* and check it's value
                return true;
            });
}

void s_second_2(Vtop__Syms* __restrict vlSymsp) {
    VL_WRITEF("TODO: $display After wait: (...)\n");

    p_second.run_conditions.push_back([](Vtop__Syms* __restrict vlSymsp) {
                return e_ready_to_finish.triggered;
            });
}

void s_second_3(Vtop__Syms* __restrict vlSymsp) {
    VL_WRITEF("TODO: $display After ready to finish: (...)\n");

    VL_WRITEF("All done!\n");
    VL_FINISH_MT("top.sv", 44, "");
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
    // XXX TODO the actual execution happens here (!!!)
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
