#include "DAG.h"
#include "repcut.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <vector>

namespace fs = std::filesystem;
static void require(bool value) { if (!value) throw std::runtime_error("Memory API test failed"); }
struct Input {
    std::vector<float> weights;
    std::vector<size_t> offsets{0};
    std::vector<uint32_t> neighbors;
    explicit Input(unsigned n) {
        for (unsigned i = 0; i < n; ++i) {
            weights.push_back(0.25f + i % 5);
            for (unsigned j : {i, (i + 1) % n, (i + 7) % n}) neighbors.push_back(n + j);
            offsets.push_back(neighbors.size());
        }
        for (unsigned i = 0; i < n; ++i) {
            weights.push_back(1 + i % 3);
            offsets.push_back(neighbors.size());
        }
    }
    RepCutGraph view() const { return {static_cast<uint32_t>(weights.size()), neighbors.size(), weights.data(), offsets.data(), neighbors.data()}; }
    void save() const {
        std::ofstream out("input.graph");
        out << neighbors.size() << ' ' << weights.size() << '\n';
        for (size_t i = 0; i < weights.size(); ++i) {
            out << "n " << weights[i];
            for (size_t j = offsets[i]; j < offsets[i + 1]; ++j) out << ' ' << neighbors[j];
            out << '\n';
        }
    }
};
struct Output {
    std::vector<std::vector<uint32_t>> parts;
    bool reject = false;
    const RepCutContext* nested = nullptr;
    const RepCutGraph* graph = nullptr;
    static int collect(void* user, uint32_t part, const uint32_t* ids, size_t n) {
        auto& out = *static_cast<Output*>(user);
        if (out.reject || part != out.parts.size()) return 1;
        if (out.nested) {
            // Both entry points must share the process-wide busy guard.
            if (repcut_run(out.nested, nullptr) == 0
                || repcut_run_graph(out.nested, out.graph, collect, user, nullptr) == 0) return 1;
            out.nested = nullptr;
        }
        out.parts.emplace_back();
        if (n) out.parts.back().assign(ids, ids + n);
        return 0;
    }
    std::string csv() const {
        std::ostringstream out;
        for (const auto& part : parts) {
            for (auto id : part) out << id << ',';
            out << '\n';
        }
        return out.str();
    }
};
static void checkDag(Input& input) {
    input.save();
    repcut::DirectedAcyclicGraph file, memory;
    require(file.buildFromFile("input.graph"));
    require(memory.buildFromMemory(input.view()));
    require(file.weight == memory.weight && file.valid == memory.valid);
    for (size_t i = 0; i < file.numVertices(); ++i) {
        for (bool incoming : {false, true}) {
            auto a = incoming ? file.inNeigh[i] : file.outNeigh[i];
            auto b = incoming ? memory.inNeigh[i] : memory.outNeigh[i];
            require(std::vector<uint32_t>(a.begin(), a.end()) == std::vector<uint32_t>(b.begin(), b.end()));
        }
    }
}
int main(int argc, char** argv) {
    try {
        require(argc == 5);
        const std::string mode = argv[1];
        fs::create_directories(argv[2]);
        fs::current_path(argv[2]);
        Input input(128);
        auto graph = input.view();
        RepCutContext ctx{nullptr, nullptr, 4, 0.03f, 1, std::stoi(argv[3]), REPCUT_LOG_SILENT, nullptr, false};
        RepCutStatistics stats{};
        Output output;
        if (mode == "file") {
            input.save(); ctx.graph_filename = "input.graph"; ctx.work_directory = ".";
            require(repcut_run(&ctx, &stats) == 0);
            std::ifstream in("rcp_output.txt");
            std::cout << in.rdbuf();
        } else {
            // Invalid paths must be ignored when dumps are disabled.
            ctx.graph_filename = "missing/graph"; ctx.work_directory = "missing/work";
            require(repcut_run_graph(&ctx, &graph, Output::collect, &output, &stats) == 0);
            require(fs::is_empty("."));
            std::cout << output.csv();
            if (mode == "checks") {
                // Structural parity includes duplicate edges and invalid/zero-weight nodes.
                input.weights[0] = -1; input.weights[1] = 0;
                input.neighbors[4] = input.neighbors[3];
                checkDag(input);
                input = Input(128); graph = input.view();
                Output rejected; rejected.reject = true;
                require(repcut_run_graph(&ctx, &graph, Output::collect, &rejected, nullptr) != 0);
                for (int kind = 0; kind < 6; ++kind) {
                    auto bad = graph;
                    if (kind == 0) bad.offsets = nullptr;
                    if (kind == 1) bad.neighbors = nullptr;
                    if (kind == 2) ++bad.num_edges;
                    if (kind == 3) input.offsets[1] = graph.num_edges + 1;
                    if (kind == 4) input.neighbors[0] = graph.num_vertices;
                    if (kind == 5) input.weights[0] = std::numeric_limits<float>::quiet_NaN();
                    require(repcut_run_graph(&ctx, &bad, Output::collect, &output, nullptr) != 0);
                    input = Input(128); graph = input.view();
                }
                require(repcut_run_graph(&ctx, nullptr, Output::collect, &output, nullptr) != 0);
                require(repcut_run_graph(&ctx, &graph, nullptr, &output, nullptr) != 0);
                for (int i = 0; i < 8; ++i) {
                    Output next; next.nested = i == 0 ? &ctx : nullptr; next.graph = &graph;
                    require(repcut_run_graph(&ctx, &graph, Output::collect, &next, nullptr) == 0);
                    require(next.parts.size() == 4);
                }
                // The graph API must not write a configuration file, even transiently.
                fs::create_directory("mtkahypar.ini");
                std::ofstream("mtkahypar.ini/sentinel") << "preserve\n";
                Output blocked_path;
                require(repcut_run_graph(&ctx, &graph, Output::collect, &blocked_path, nullptr) == 0);
                require(blocked_path.parts.size() == 4);
                require(fs::is_regular_file("mtkahypar.ini/sentinel"));
                fs::remove("mtkahypar.ini/sentinel");
                fs::remove("mtkahypar.ini");
                Input empty(0); auto emptyGraph = empty.view(); Output emptyOutput;
                require(repcut_run_graph(&ctx, &emptyGraph, Output::collect, &emptyOutput, nullptr) == 0);
                require(emptyOutput.parts.size() == 4);
                ctx.save_intermediate_files = true; ctx.work_directory = ".";
                Output saved;
                require(repcut_run_graph(&ctx, &graph, Output::collect, &saved, nullptr) == 0);
                require(fs::exists("parts.hmetis") && !fs::exists("rcp_output.txt") && !fs::exists(".lock"));
            }
        }
        std::ofstream stat(argv[4]);
        stat << std::setprecision(std::numeric_limits<float>::max_digits10)
             << stats.nparts << ' ' << stats.sg_size << ' ' << stats.total_part_size << ' '
             << stats.replication_size << ' ' << stats.sg_weight << ' ' << stats.total_part_weight << ' '
             << stats.ib_factor_weight << ' ' << stats.replication_weight << ' ' << stats.replication_rate_weight << ' '
             << stats.ib_factor_size << ' ' << stats.replication_rate_size << '\n';
    } catch (const std::exception& error) { std::cerr << error.what() << '\n'; return 1; }
}
