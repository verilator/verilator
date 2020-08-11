#include "Vtest.h"
#include "verilated.h"

int main(int argc, char** argv, char** env) {

    Verilated::commandArgs(argc, argv);
    Vtest* top = new Vtest;

    int cnt = 0;

    while (!Verilated::gotFinish()) { 
        cnt++;
        top->eval(); 
        if (cnt > 1000)
            top->b = 1;
        else
            top->b = 0;
    }

    delete top;
    exit(0);
}
