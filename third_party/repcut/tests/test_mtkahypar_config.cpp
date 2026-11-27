#include "MtKaHyPar.h"

#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/partition/context.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>

namespace fs = std::filesystem;
using Context = std::unique_ptr<mt_kahypar_context_t, decltype(&mt_kahypar_free_context)>;

static void require(bool condition, const char* message)
{
    if (!condition)
        throw std::runtime_error(message);
}

static void checkTextLoading(const fs::path& directory)
{
    const char* text = "preset-type=default\nmode=direct\np-louvain-low-memory-contraction=true\n";
    const auto file = directory / "loader.ini";
    std::ofstream(file) << text;
    mt_kahypar_error_t error{};
    const Context from_file(mt_kahypar_context_from_file(file.string().c_str(), &error), mt_kahypar_free_context);
    const Context from_text(mt_kahypar_context_from_string(text, &error), mt_kahypar_free_context);
    require(from_file && from_text, "Cannot load matching file and text contexts");
    auto& file_config = *reinterpret_cast<mt_kahypar::Context*>(from_file.get());
    auto& text_config = *reinterpret_cast<mt_kahypar::Context*>(from_text.get());
    require(file_config.preprocessing.community_detection.low_memory_contraction &&
                text_config.preprocessing.community_detection.low_memory_contraction,
            "INI loader lost the low-memory option");
    file_config.partition.verbose_logging = true;
    text_config.partition.verbose_logging = true;
    std::ostringstream file_dump, text_dump;
    file_dump << file_config;
    text_dump << text_config;
    require(file_dump.str() == text_dump.str(), "File and text INI loaders differ");
    fs::remove(file);
    require(!mt_kahypar_context_from_file(file.string().c_str(), &error), "Missing INI file was accepted");
    mt_kahypar_free_error_content(&error);
    for (const char* invalid :
         {static_cast<const char*>(nullptr), "unknown-option=true\n", "p-max-louvain-pass-iterations=not-a-number\n"}) {
        const Context bad(mt_kahypar_context_from_string(invalid, &error), mt_kahypar_free_context);
        require(!bad && error.status != SUCCESS && error.msg, "Invalid INI text was accepted");
        mt_kahypar_free_error_content(&error);
    }
    const Context recovered(mt_kahypar_context_from_string(text, &error), mt_kahypar_free_context);
    require(recovered != nullptr, "Text loader did not recover after a parse error");
}

int main(int argc, char** argv)
{
    try {
        require(argc == 2, "Usage: test-mtkahypar-config WORKDIR");
        SpinLock owner;
        require(owner.tryLock(), "Cannot acquire free serial owner");
        require(!owner.tryLock(), "Serial ownership was lost");
        SpinLock copied(owner);
        require(copied.tryLock(), "Copied serial owner should be free");
        copied.unlock();
        copied.lock();
        copied = owner;
        require(copied.tryLock(), "Assigned serial owner should be free");
        copied.unlock();
        owner.unlock();
        owner.lock();
        require(!owner.tryLock(), "Serial lock did not retain ownership");
        owner.unlock();
        const auto directory = fs::absolute(argv[1]);
        fs::create_directories(directory);
        fs::current_path(directory);
        const fs::path file = directory / "mtkahypar.ini";
        fs::create_directory(file);
        std::ofstream(file / "sentinel") << "preserve\n";
        mt_kahypar_initialize(1, false);
        const Context actual(repcut::makeMtKaHyParContext(), mt_kahypar_free_context);
        const Context baseline(mt_kahypar_context_from_preset(DEFAULT), mt_kahypar_free_context);
        require(actual && baseline, "Cannot create contexts");

        auto& config = *reinterpret_cast<mt_kahypar::Context*>(actual.get());
        auto& original = *reinterpret_cast<mt_kahypar::Context*>(baseline.get());
        require(config.preprocessing.community_detection.low_memory_contraction,
                "Linked backend did not enable low-memory contraction");
        require(!original.preprocessing.community_detection.low_memory_contraction,
                "Upstream default changed; review RepCut's override");
        require(config.preprocessing.use_community_detection, "Community detection was disabled");
        require(mt_kahypar_get_preset(actual.get()) == DEFAULT, "Wrong preset");
        // The verbose diagnostic includes the other preset options, but not the
        // low-memory flag; compare them to detect an incomplete configuration.
        config.partition.verbose_logging = true;
        original.partition.verbose_logging = true;
        std::ostringstream configured, defaults;
        configured << config;
        defaults << original;
        require(configured.str() == defaults.str(), "Other default preset parameters changed");

        // A directory at the old temporary filename must not affect loading.
        require(fs::is_regular_file(file / "sentinel"), "Context loading touched the old temporary path");
        std::ifstream sentinel(file / "sentinel");
        std::string content;
        std::getline(sentinel, content);
        require(content == "preserve", "Context loading changed the sentinel");
        sentinel.close();
        fs::remove(file / "sentinel");
        fs::remove(file);
        const Context repeated(repcut::makeMtKaHyParContext(), mt_kahypar_free_context);
        require(repeated && !fs::exists(file), "Context loading created a temporary file");
        checkTextLoading(directory);
        std::cout << "Linked low-memory configuration, preset preservation and memory parsing passed\n";
    }
    catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
