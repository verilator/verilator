#pragma once

#include <atomic>
#include <iostream>
#include <tbb/task_scheduler_observer.h>
#include <thread>

namespace whfc {

    class pinning_observer : public tbb::task_scheduler_observer {
        size_t ncpus;

    public:
        pinning_observer() : ncpus(std::thread::hardware_concurrency()) {}

        void on_scheduler_entry(bool) {
            const size_t size = CPU_ALLOC_SIZE(ncpus);
            int slot = tbb::this_task_arena::current_thread_index();
            cpu_set_t target_mask;
            CPU_ZERO(&target_mask);
            CPU_SET(slot, &target_mask);
            const int err = sched_setaffinity(0, size, &target_mask);
            if (err) {
                std::cout << "Failed to set thread affinity" << std::endl;
                std::exit(EXIT_FAILURE);
            }
        }
    };

} // namespace whfc
