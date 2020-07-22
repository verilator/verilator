/*
 * Top level simulation driver for use with verilator
 */

#include <verilated.h>
#include <Vtop.h>

vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char *argv[]) {
	Verilated::commandArgs(argc, argv);

	Vtop *top = new Vtop;

	for (; main_time < 1000 && !Verilated::gotFinish(); ++main_time) {
		top->eval();
	}

	top->final();

	delete top;

	return 0;
}
