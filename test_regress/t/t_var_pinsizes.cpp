// -*- mode: C++; c-file-style: "cc-mode" -*-

#ifdef T_VAR_PINS_CC
# include "Vt_var_pins_cc.h"
#elif defined(T_VAR_PINS_SC1)
# include "Vt_var_pins_sc1.h"
#elif defined(T_VAR_PINS_SC2)
# include "Vt_var_pins_sc2.h"
#elif defined(T_VAR_PINS_SC32)
# include "Vt_var_pins_sc32.h"
#elif defined(T_VAR_PINS_SC64)
# include "Vt_var_pins_sc64.h"
#elif defined(T_VAR_PINS_SCUI)
# include "Vt_var_pins_scui.h"
#elif defined(T_VAR_PINS_SC_UINT)
# include "Vt_var_pins_sc_uint.h"
#elif defined(T_VAR_PINS_SC_BIGUINT)
# include "Vt_var_pins_sc_biguint.h"
#elif defined(T_VAR_PINS_SC_UINT_BIGUINT)
# include "Vt_var_pins_sc_uint_biguint.h"
#else
# error "Unknown test"
#endif

VM_PREFIX* tb = NULL;

double sc_time_stamp() {
    return 0;
}

int main() {
    Verilated::debug(0);
    tb  = new VM_PREFIX("tb");

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    return 0;
}

int sc_main(int argc, char *argv[]) {
    tb  = new VM_PREFIX("tb");

    VL_PRINTF("*-* All Finished *-*\n");
    tb->final();
    return 0;
}
