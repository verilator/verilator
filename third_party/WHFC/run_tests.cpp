#include "tests/flow_hypergraph_tests.h"
#include "tests/subset_sum_tests.h"

int main(int argc, char* argv[]) {
    whfc::Test::SubsetSumTests().run();
    whfc::Test::FlowHypergraphTests().run();
    return 0;
}
