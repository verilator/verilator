#pragma once

#include <chrono>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace whfc {
    using Interval = std::chrono::duration<double>;
    using Timepoint = std::chrono::time_point<std::chrono::high_resolution_clock>;

    inline Timepoint time_now() { return std::chrono::high_resolution_clock::now(); }

    template<typename resolution>
    std::chrono::duration<double, std::milli> inMilliseconds(std::chrono::duration<double, resolution> dur) {
        return dur;
    }
    template<typename resolution>
    std::chrono::duration<double> inSeconds(std::chrono::duration<double, resolution> dur) {
        return dur;
    }


    class TimeReporter {
    public:
        using Identifier = std::string;

        TimeReporter() = default;
        TimeReporter(const Identifier& top_level_category) : top_level_category(top_level_category) {}

        void start(const Identifier& id, const Identifier& parent_id) {
            if (!active)
                return;
            auto start_running = running.try_emplace(id, time_now());
            if (!start_running.second)
                throw std::logic_error("Measurement " + id + " still running.");
            registerCategory(id, parent_id);
        }

        void start(const Identifier& id) { start(id, top_level_category); }

        void stop(const Identifier& id) {
            if (!active)
                return;
            auto t = time_now();
            auto r = running.find(id);
            if (r == running.end())
                throw std::logic_error("Measurement " + id + " not running");
            times.at(id) += (t - r->second);
            running.erase(r);
        }

        void start() { start(top_level_category); }

        void stop() { stop(top_level_category); }

        void report(std::ostream& os) {
            if (!active)
                return;
            std::vector<std::pair<std::string, std::string>> lines;
            traverseTree(lines, top_level_category, 0);

            size_t min_padding = 6;
            size_t max_left = 0, max_right = 0;
            for (auto& l : lines) {
                max_left = std::max(max_left, l.first.size());
                max_right = std::max(max_right, l.second.size());
            }

            size_t line_width = min_padding + max_left + max_right;
            std::string header = "Running time report";
            os << header;
            for (size_t i = header.length(); i < line_width; ++i)
                os << "-";
            os << "\n";
            for (auto& l : lines) {
                os << l.first;
                size_t padding = line_width - (l.first.size() + l.second.size());
                for (size_t i = 0; i < padding; ++i)
                    os << " ";
                os << l.second << "\n";
            }

            for (size_t i = 0; i < line_width; ++i)
                os << "-";
            os << std::endl;
        }

        void registerCategory(const Identifier& id, const Identifier& parent) {
            auto start_category = times.try_emplace(id, Interval(0.0));
            if (start_category.second && id != parent)
                tree[parent].push_back(id);
        }

        void registerCategory(const Identifier& id) { registerCategory(id, top_level_category); }

        Interval get(const Identifier& cat) { return times[cat]; }

        void clear() {
            running.clear();
            times.clear();
            tree.clear();
        }

        bool active = true;
        Identifier top_level_category = "total";

    private:
        void traverseTree(std::vector<std::pair<std::string, std::string>>& lines, const Identifier& cat, const size_t depth) {
            std::stringstream first_column;
            for (size_t i = 0; i < depth; ++i)
                first_column << "    ";
            first_column << cat;

            std::stringstream second_column;
            second_column << std::fixed << std::setprecision(4);
            auto ret = times.find(cat);
            if (ret != times.end())
                second_column << ret->second.count() << " s";
            else {
                if (cat != top_level_category) {
                    second_column << " --- ";
                } else {
                    Interval sum(0.0);
                    for (Identifier child : tree[cat]) {
                        auto ret_top = times.find(child);
                        sum += ret_top == times.end() ? Interval(0.0) : ret_top->second;
                    }
                    second_column << sum.count() << " s";
                }
            }


            lines.emplace_back(first_column.str(), second_column.str());
            for (Identifier child : tree[cat])
                traverseTree(lines, child, depth + 1);
        }

        std::unordered_map<Identifier, Timepoint> running;
        std::unordered_map<Identifier, Interval> times;
        std::unordered_map<Identifier, std::vector<Identifier>> tree;
    };


} // namespace whfc
