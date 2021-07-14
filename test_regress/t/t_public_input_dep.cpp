// Test defines
#define MAIN_TIME_MULTIPLIER 1
#include <memory>
// OS header
#include "verilatedos.h"
// Generated header
#include "Vt_public_input_dep.h"
// General headers
#include "verilated.h"
#include "verilated_vcd_c.h"

#define STRINGIFY(x) STRINGIFY2(x)
#define STRINGIFY2(x) #x

std::unique_ptr<Vt_public_input_dep> topp;
int main(int argc, char** argv, char** env) {
    vluint64_t sim_time = 1100;
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    srand48(5);
    topp.reset(new Vt_public_input_dep("top"));

#if VM_TRACE
    Verilated::traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    topp->clk = 0;
    topp->eval();
    {
        contextp->timeInc(10 * MAIN_TIME_MULTIPLIER);
    }

#if VM_TRACE
    if (tfp) tfp->dump(contextp->time());
#endif
    while ((contextp->time() < sim_time * MAIN_TIME_MULTIPLIER)
           && !contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->t__DOT__clk_1[1] = !topp->t__DOT__clk_1[1];
        topp->eval();
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);

#if VM_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    topp.reset();
    return 0;
}
