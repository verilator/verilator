#include "Vadd1_py.h"
#include "Vadd2_py.h"

//Declare a pybind11 module
PYBIND11_MODULE(example, m) {
    m.doc() = "Example verilog wapper in python";

    //declare_globals declares the common parts of verilator (Verilated class and tracing classes)
    vl_py::declare_globals(m);
    //Call declare_* for each toplevel verilator module. 1 per verilate() call in CMakeLists.txt
    vl_py::declare_Vadd1(m);
    vl_py::declare_Vadd2(m);
}
