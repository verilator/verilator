# Check wether SSE4.2 & AVX ISA extensions are available.

include(CheckSourceRuns)
include(CMakePushCheckState)

# Check SSE4.2 support
cmake_push_check_state(RESET)
    set(CMAKE_REQUIRED_QUIET TRUE)
    if(NOT MSVC)
        set(CMAKE_REQUIRED_FLAGS "-msse4.2")
    endif()
    check_source_runs(CXX [[
        #include <nmmintrin.h>
        int main() {
            volatile auto tmp = _mm_crc32_u64(0, 0);
            return 0;
        }
    ]] SUPPORTS_SSE4_2)
cmake_pop_check_state()

# Check AVX support
cmake_push_check_state(RESET)
    set(CMAKE_REQUIRED_QUIET TRUE)
    if(NOT MSVC)
        set(CMAKE_REQUIRED_FLAGS "-mavx")
    endif()
    check_source_runs(CXX [[
        #include <immintrin.h>
        int main() {
            volatile auto tmp = _mm256_setzero_ps();
            return 0;
        }
    ]] SUPPORTS_AVX)
cmake_pop_check_state()
