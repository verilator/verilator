#include "repcut.h"

#include <cmath>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

namespace fs = std::filesystem;

static void require(bool condition, const char* message)
{
    if (!condition)
        throw std::runtime_error(message);
}

static std::string read(const fs::path& path)
{
    std::ifstream file(path);
    require(file.good(), "Cannot read test output");
    return {std::istreambuf_iterator<char>(file), std::istreambuf_iterator<char>()};
}

static void writeGraph(unsigned n)
{
    std::ofstream graph("input.graph");
    graph << 3 * n << ' ' << 2 * n << '\n';
    for (unsigned i = 0; i < n; ++i)
        graph << "n " << 0.25 + i % 5 << ' ' << n + i << ' ' << n + (i + 1) % n << ' ' << n + (i + 7) % n << '\n';
    for (unsigned i = 0; i < n; ++i)
        graph << "n " << 1 + i % 3 << '\n';
}

static void checkClosure(const std::string& output, unsigned n, int k)
{
    std::vector<unsigned> owners(n);
    std::istringstream lines(output);
    std::string line;
    int parts = 0;
    while (std::getline(lines, line)) {
        ++parts;
        std::vector<bool> present(2 * n);
        std::istringstream fields(line);
        std::string field;
        while (std::getline(fields, field, ',')) {
            if (field.empty())
                continue;
            const auto node = std::stoul(field);
            require(node < 2 * n && !present[node], "Invalid or duplicate DAG node");
            present[node] = true;
        }
        for (unsigned i = 0; i < n; ++i) {
            if (present[n + i])
                ++owners[i];
            const bool needed = present[n + i] || present[n + (i + 1) % n] || present[n + (i + 7) % n];
            require(present[i] == needed, "Partition is not exactly its sinks' dependency closure");
        }
    }
    require(parts == k, "Wrong number of partitions");
    for (const auto count : owners)
        require(count == 1, "Sink must have exactly one owner");
}

static void repeat(int threads)
{
    RepCutContext ctx{"input.graph", ".", 2, 0.1f, threads, 42, REPCUT_LOG_SILENT, nullptr, false};
    for (unsigned run = 0; run < 100; ++run) {
        // Include graphs large enough to exercise MtKaHyPar's coarsening.
        const unsigned n = 128U << (run % 4);
        ctx.nparts = 1 + run % 4;
        ctx.seed = 17 + run % 5;
        writeGraph(n);
        RepCutStatistics stats{};
        require(repcut_run(&ctx, &stats) == 0, "Sequential call failed");
        require(!fs::exists(".lock"), "Work directory lock leaked");
        require(stats.nparts == static_cast<unsigned>(ctx.nparts) && stats.sg_size == 2 * n, "Incorrect statistics");
        const auto output = read("rcp_output.txt");
        checkClosure(output, n, ctx.nparts);
    }
    require(!fs::exists("parts.hmetis"), "Linked backend wrote an intermediate hypergraph");
    require(!fs::exists("mtkahypar.ini"), "Linked backend leaked its temporary configuration");

    writeGraph(32);
    fs::create_directory("saved");
    auto saved = ctx;
    saved.work_directory = "saved";
    saved.seed = 42;
    saved.save_intermediate_files = true;
    require(repcut_run(&saved, nullptr) == 0, "Saving intermediate files failed");
    require(fs::is_regular_file("saved/parts.hmetis"), "Missing saved hypergraph");
    require(fs::is_regular_file("saved/parts.hmetis.part4.epsilon0.1.seed42.KaHyPar"),
            "Missing saved cone assignments");
    checkClosure(read("saved/rcp_output.txt"), 32, saved.nparts);
    require(repcut_run(&ctx, nullptr) == 0, "Call with saving disabled failed");
    require(!fs::exists("parts.hmetis"), "Call with saving disabled saved a hypergraph");

    // Reject nonserial requests without leaking the busy or work-directory
    // guard, so a valid serial call can still follow.
    ++ctx.parallel_threads;
    require(repcut_run(&ctx, nullptr) != 0, "A nonserial thread count was accepted");
    --ctx.parallel_threads;
    ctx.seed = -1;
    require(repcut_run(&ctx, nullptr) == 0, "Call after thread-count rejection failed");
    ctx.seed = -2;
    require(repcut_run(&ctx, nullptr) != 0, "Invalid seed was accepted");
    ctx.seed = 42;
    ctx.target_ib = std::numeric_limits<float>::quiet_NaN();
    require(repcut_run(&ctx, nullptr) != 0, "Invalid imbalance was accepted");
    ctx.target_ib = 0.1f;
    std::ofstream("input.graph") << "2 3\na 4294967296 1 2\nb 1\nc 1\n";
    require(repcut_run(&ctx, nullptr) != 0, "Cluster weight overflow was accepted");
    std::ofstream("input.graph") << "2 3\na 2147483648 1 2\nb 1\nc 1\n";
    require(repcut_run(&ctx, nullptr) != 0, "Signed edge weight overflow was accepted");
    std::ofstream("input.graph") << "2 3\na 1 1 2\nb 2147483648\nc 1\n";
    require(repcut_run(&ctx, nullptr) != 0, "Signed node weight overflow was accepted");
    std::ofstream("input.graph") << "1 2\na 1 9\nb 1\n";
    require(repcut_run(&ctx, nullptr) != 0, "Malformed graph was accepted");
    writeGraph(32);
    require(repcut_run(&ctx, nullptr) == 0, "Call after input rejection failed");
    checkClosure(read("rcp_output.txt"), 32, ctx.nparts);
    int from_other_thread = 1;
    std::thread caller([&]() { from_other_thread = repcut_run(&ctx, nullptr); });
    caller.join();
    require(from_other_thread == 0, "Sequential call from a different caller thread failed");
    checkClosure(read("rcp_output.txt"), 32, ctx.nparts);

    // Independent cones bypass MtKaHyPar and keep their wider load sums.
    std::ofstream independent("input.graph");
    independent << "0 10\n";
    for (int i = 0; i < 10; ++i)
        independent << "n 1073741824\n";
    independent.close();
    require(repcut_run(&ctx, nullptr) == 0, "Independent wide weights failed");
    std::ofstream("input.graph") << "0 0\n";
    require(repcut_run(&ctx, nullptr) == 0, "Empty graph failed");
    require(!fs::exists(".lock"), "Work directory lock leaked on error");
    std::cout << "100 sequential calls, dependency closure and error recovery passed\n";
}

static void externalDisabled()
{
    writeGraph(16);
    fs::remove("rcp_output.txt");
    RepCutContext ctx{"input.graph", ".", 2, 0.1f, 1, 42, REPCUT_LOG_SILENT, "unused-MtKaHyPar", false};
    require(repcut_run(&ctx, nullptr) != 0, "Executable override was accepted");
    require(!fs::exists(".lock"), "Lock leaked after executable rejection");
    require(!fs::exists("rcp_output.txt"), "Rejected call wrote a partition");
    ctx.mtkahypar_bin = nullptr;
    require(repcut_run(&ctx, nullptr) == 0, "Linked call after rejection failed");
    const auto output = read("rcp_output.txt");
    checkClosure(output, 16, ctx.nparts);
    ctx.mtkahypar_bin = "";
    require(repcut_run(&ctx, nullptr) == 0, "Empty override did not select linked backend");
    require(read("rcp_output.txt") == output, "Linked partition changed with empty override");
    require(!fs::exists(".lock"), "Work directory lock leaked");
    std::cout << "Executable rejection and linked-library recovery passed\n";
}

static void serialOnly()
{
    writeGraph(16);
    fs::remove("rcp_output.txt");
    RepCutContext ctx{"input.graph", ".", 2, 0.1f, 1, 42, REPCUT_LOG_SILENT, nullptr, false};
    for (int threads : {0, 2, -1}) {
        ctx.parallel_threads = threads;
        require(repcut_run(&ctx, nullptr) != 0, "Nonserial thread count was accepted");
        require(!fs::exists("rcp_output.txt") && !fs::exists(".lock"), "Rejected call wrote files");
    }
    ctx.parallel_threads = 1;
    require(repcut_run(&ctx, nullptr) == 0, "Serial call after rejection failed");
    checkClosure(read("rcp_output.txt"), 16, ctx.nparts);
}

int main(int argc, char** argv)
{
    try {
        require(argc >= 3, "Usage: test-library repeat|external-disabled WORKDIR [THREADS]");
        fs::create_directories(argv[2]);
        fs::current_path(argv[2]);
        if (std::string(argv[1]) == "repeat") {
            require(argc == 4, "Missing thread count");
            repeat(std::stoi(argv[3]));
        }
        else if (std::string(argv[1]) == "serial-only") {
            serialOnly();
        }
        else {
            require(std::string(argv[1]) == "external-disabled", "Unknown test case");
            externalDisabled();
        }
    }
    catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
