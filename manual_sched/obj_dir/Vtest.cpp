// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtest.h for the primary calling header

#include "Vtest.h"
#include "Vtest__Syms.h"

#include <list>
#include <vector>

//==========

void list_init(void);

void Vtest::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vtest::eval\n"); );
    Vtest__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
#ifdef VL_DEBUG
    // Debug assertions
    _eval_debug_assertions();
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        list_init();
        _eval_initial_loop(vlSymsp);
    }
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("test.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void Vtest::_eval_initial_loop(Vtest__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    _eval_initial(vlSymsp);
    _eval_re_initial(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        _eval_settle(vlSymsp);
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("test.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void Vtest::_combo__TOP__2(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_combo__TOP__2\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->e = vlTOPp->f;
}

/**************************/

typedef bool (*cond_funcp)(Vtest__Syms*);
typedef void (*eval_funcp)(Vtest__Syms*);

typedef enum region_no
{
    ACTIVE = 0,
    INACTIVE = 1,
    NBA = 2,
    REACTIVE = 3,
    REINACTIVE = 4,
    RENBA = 5,
    REG_MAX = 6
} region_no;

typedef unsigned long long timeslot_t;
typedef std::tuple<cond_funcp, eval_funcp, region_no> cond_tuple_t;
typedef std::tuple<timeslot_t, eval_funcp, region_no> time_tuple_t;

typedef std::list<cond_tuple_t> cond_list_t;
typedef std::list<time_tuple_t> time_list_t;

cond_list_t cond_list, next_cond_list;
time_list_t time_list;
std::list<eval_funcp> regions[REG_MAX];
timeslot_t curr_timeslot = 0;

bool _sequent__TOP__4_cond(Vtest__Syms* __restrict vlSymsp) {
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;

    return (((IData)(vlTOPp->clk1) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk1))));
}

bool _sequent__TOP__5_cond(Vtest__Syms* __restrict vlSymsp) {
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;

    return (((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))));
}

void _sequent__TOP__4(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__4\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    VL_WRITEF("clk1 %1#\n",1,vlTOPp->d);

    // Final
    next_cond_list.push_back(cond_tuple_t {_sequent__TOP__4_cond, _sequent__TOP__4, ACTIVE});
}

void _sequent__TOP__5(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__5\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if (VL_UNLIKELY(vlTOPp->b)) {
        VL_FINISH_MT("test.v", 10, "");
    }
    VL_WRITEF("other block0 %1# %1#\n",1,vlTOPp->a,
              1,(IData)(vlTOPp->c));
    VL_WRITEF("same block1 %1# %1#\n",1,vlTOPp->a,1,
              (IData)(vlTOPp->c));
    VL_WRITEF("other block2 %1# %1#\n\n",1,vlTOPp->a,
              1,(IData)(vlTOPp->c));
    VL_WRITEF("same block0 %1# %1#\n",1,vlTOPp->a,1,
              (IData)(vlTOPp->c));

    // Final
    next_cond_list.push_back(cond_tuple_t {_sequent__TOP__5_cond, _sequent__TOP__5, ACTIVE});
}

/*

always begin
    #20
    clk = 0;
    #20
    clk = 1;
end

*/

/***/

void _sequent__TOP__6_P0(Vtest__Syms* __restrict vlSymsp);

bool _sequent__TOP__6_cond(Vtest__Syms* __restrict vlSymsp) {
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;

    return true;
}

void _sequent__TOP__6_P2(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__6_P2\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->clk = 1;
    // Final
    next_cond_list.push_back(cond_tuple_t {_sequent__TOP__6_cond, _sequent__TOP__6_P0, ACTIVE});
}

void _sequent__TOP__6_P1(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__6P1\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->clk = 0;
    // Final
    time_list.push_back(time_tuple_t {curr_timeslot+20, _sequent__TOP__6_P2, ACTIVE});
}

void _sequent__TOP__6_P0(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__6P0\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Final
    time_list.push_back(time_tuple_t {curr_timeslot+20, _sequent__TOP__6_P1, ACTIVE});
}

/***/

void _sequent__TOP__4_NBA(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__4_NBA\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->d = (1U & (~ (IData)(vlTOPp->d)));
    // Final
    next_cond_list.push_back(cond_tuple_t {_sequent__TOP__4_cond, _sequent__TOP__4_NBA, NBA});
}

void _sequent__TOP__5_NBA(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_sequent__TOP__5_NBA\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->a = (1U & (~ (IData)(vlTOPp->a)));
    vlTOPp->c = vlTOPp->a;
    // Final
    next_cond_list.push_back(cond_tuple_t {_sequent__TOP__5_cond, _sequent__TOP__5_NBA, NBA});
}

void list_init(void) {
    cond_list.push_back(cond_tuple_t {_sequent__TOP__4_cond, _sequent__TOP__4, ACTIVE});
    cond_list.push_back(cond_tuple_t {_sequent__TOP__4_cond, _sequent__TOP__4_NBA, NBA});

    cond_list.push_back(cond_tuple_t {_sequent__TOP__5_cond, _sequent__TOP__5, ACTIVE});
    cond_list.push_back(cond_tuple_t {_sequent__TOP__5_cond, _sequent__TOP__5_NBA, NBA});

    cond_list.push_back(cond_tuple_t {_sequent__TOP__6_cond, _sequent__TOP__6_P0, ACTIVE});
}

void _evalDelays(void) {
    auto i = time_list.begin();
    do {
        if (std::get<0>(*i) == curr_timeslot) {
            regions[std::get<2>(*i)].push_back(std::get<1>(*i));
            time_list.erase(i++);
        } else {
            i++;
        }
    } while (i != time_list.end());
}

void _evalRegion(Vtest__Syms* __restrict vlSymsp, region_no base_reg) {
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;

    do {
        for (auto p: regions[base_reg]) {
            p(vlSymsp);
        }
        regions[base_reg].clear();

        for (auto r = base_reg+INACTIVE; r < base_reg+REACTIVE; r++) {
            if (!regions[r].empty()) {
                regions[base_reg].splice(regions[base_reg].end(), regions[r]);
                break;
            }
        }

        auto i = cond_list.begin();
        do {
            if (std::get<0>(*i)(vlSymsp)) {
                regions[std::get<2>(*i)].push_back(std::get<1>(*i));
                cond_list.erase(i++);
            } else {
                i++;
            }
        } while (i != cond_list.end());
    } while (!regions[base_reg].empty());
}

void Vtest::_eval(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_eval\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body

    _evalDelays();

    do {
        _evalRegion(vlSymsp, ACTIVE);
        _evalRegion(vlSymsp, REACTIVE);
    } while (!regions[ACTIVE].empty());

    cond_list.splice(cond_list.end(), next_cond_list);
 
    // Final
    curr_timeslot++;
    vlTOPp->__Vclklast__TOP__clk1 = vlTOPp->clk1;
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
}

/**************************/

VL_INLINE_OPT QData Vtest::_change_request(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_change_request\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (// CCall type: NONE
        vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData Vtest::_change_request_1(Vtest__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_change_request_1\n"); );
    Vtest* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void Vtest::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtest::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((b & 0xfeU))) {
        Verilated::overWidthError("b");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((clk1 & 0xfeU))) {
        Verilated::overWidthError("clk1");}
    if (VL_UNLIKELY((f & 0xfeU))) {
        Verilated::overWidthError("f");}
}
#endif  // VL_DEBUG
