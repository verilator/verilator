#pragma once

#include <cstdint>
#include <memory>
#if defined(__x86_64__) && defined(__linux__)
#define FIBER_LINUX_X64
#endif

namespace VlFiberInternal {

using FiberFn = std::function<void()>;

std::uintptr_t alignDown(std::uint8_t* ptr, std::uintptr_t align) {
    return reinterpret_cast<std::uintptr_t>(ptr) & ~(align - 1);
}

#if defined(FIBER_LINUX_X64)
#include <unistd.h>

#include <sys/mman.h>
using Register = std::uintptr_t;

struct __attribute__((packed)) Context {
    Register rsp;
    Register rbp;
    Register rip;
};

// Set maximum stack size to 16MB
static constexpr std::size_t stackSize = 16 * (1 << 20);

Context setupFiber(FiberFn f, std::size_t stackSize) {
    // Get system page size for guard page alignment
    Context ctx;
    const long pageSize = ::sysconf(_SC_PAGESIZE);
    if (VL_UNLIKELY(pageSize <= 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "sysconf(_SC_PAGESIZE) failed");
    }

    // Allocate memory with mmap (anonymous, private mapping)
    void* const mappingp = ::mmap(nullptr, stackSize + 2 * pageSize, PROT_READ | PROT_WRITE,
                                  MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (VL_UNLIKELY(mappingp == MAP_FAILED)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"mmap failed: "} + std::strerror(errno)).c_str());
    }

    // Initialize memory layout pointers
    ctx.rsp = alignDown(static_cast<std::uintptr_t>(mappingp) + stackSize + pageSize - 1, 16);
    ctx.rbp = 0;
    ctx.rip = std::addressof(f);

    // Protect guard pages (no read/write access) to catch stack overflow/underflow
    uint8_t* const lowGuard = static_cast<uint8_t*>(mappingp);
    uint8_t* const highGuard = static_cast<uint8_t*>(alignDown(ctx.rsp, pageSize));

    if (VL_UNLIKELY(::mprotect(lowGuard, guardSize, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for low guard page");
    }
    if (VL_UNLIKELY(::mprotect(highGuard, guardSize, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for high guard page");
    }
    return ctx;
}

#endif

};  //namespace VlFiberInternal
