#include "verilatedos.h"

#include <mutex>

#define NO_ANNOTATION

// clang-format off
#define TEST(MAIN_ANNOTATION, SUB_FUNCTION) \
    static void t_ ## SUB_FUNCTION ## _from_ ## MAIN_ANNOTATION ## _e() MAIN_ANNOTATION { SUB_FUNCTION(); }

#define TEST2(MAIN_ANNOTATION, X, SUB_FUNCTION) \
    static void t_ ## SUB_FUNCTION ## _from_ ## MAIN_ANNOTATION ## _e() MAIN_ANNOTATION(X) { SUB_FUNCTION(); }
// clang-format on

static std::mutex m_mutex;
static void no_attributes_function();
static void mt_unsafe_function() VL_MT_UNSAFE;
static void mt_unsafe_one_function() VL_MT_UNSAFE_ONE;
static void mt_safe_function() VL_MT_SAFE;
static void mt_pure_function() VL_PURE;
static void mt_safe_postinit_function() VL_MT_SAFE_POSTINIT;
static void mt_safe_excludes_function() VL_MT_SAFE_EXCLUDES(m_mutex);
static void mt_start_function() VL_MT_START;

class good {
    // function that doesn't have any annotations
    // can use all possible functions without any warning
    TEST(NO_ANNOTATION, no_attributes_function);
    TEST(NO_ANNOTATION, mt_unsafe_function);
    TEST(NO_ANNOTATION, mt_unsafe_one_function);
    TEST(NO_ANNOTATION, mt_safe_function);
    TEST(NO_ANNOTATION, mt_pure_function);
    TEST(NO_ANNOTATION, mt_safe_postinit_function);
    TEST(NO_ANNOTATION, mt_safe_excludes_function);
    TEST(NO_ANNOTATION, mt_start_function);
    // pure functions can only call another pure function
    TEST(VL_PURE, mt_pure_function);
    // mt_safe can call other mt_safe function, or
    // pure function
    TEST(VL_MT_SAFE, mt_safe_function);
    TEST(VL_MT_SAFE, mt_pure_function);
    TEST(VL_MT_SAFE, mt_safe_postinit_function);
    TEST(VL_MT_SAFE, mt_safe_excludes_function);
    // mt_safe_postinit can call other mt_safe function, or
    // pure function
    TEST(VL_MT_SAFE_POSTINIT, mt_safe_function);
    TEST(VL_MT_SAFE_POSTINIT, mt_pure_function);
    TEST(VL_MT_SAFE_POSTINIT, mt_safe_postinit_function);
    TEST(VL_MT_SAFE_POSTINIT, mt_safe_excludes_function);
    // mt_safe_excludes can call other mt_safe function, or
    // pure function
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_safe_function);
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_pure_function);
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_safe_postinit_function);
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_safe_excludes_function);
    // mt_unsafe can use all possible functions
    TEST(VL_MT_UNSAFE, no_attributes_function);
    TEST(VL_MT_UNSAFE, mt_unsafe_function);
    TEST(VL_MT_UNSAFE, mt_unsafe_one_function);
    TEST(VL_MT_UNSAFE, mt_safe_function);
    TEST(VL_MT_UNSAFE, mt_pure_function);
    TEST(VL_MT_UNSAFE, mt_safe_postinit_function);
    TEST(VL_MT_UNSAFE, mt_safe_excludes_function);
    TEST(VL_MT_UNSAFE, mt_start_function);
    // mt_unsafe_one can use all possible functions
    TEST(VL_MT_UNSAFE_ONE, no_attributes_function);
    TEST(VL_MT_UNSAFE_ONE, mt_unsafe_function);
    TEST(VL_MT_UNSAFE_ONE, mt_unsafe_one_function);
    TEST(VL_MT_UNSAFE_ONE, mt_safe_function);
    TEST(VL_MT_UNSAFE_ONE, mt_pure_function);
    TEST(VL_MT_UNSAFE_ONE, mt_safe_postinit_function);
    TEST(VL_MT_UNSAFE_ONE, mt_safe_excludes_function);
    TEST(VL_MT_UNSAFE_ONE, mt_start_function);
    // mt_start can call mt_safe function, or
    // pure function
    TEST(VL_MT_START, mt_safe_function);
    TEST(VL_MT_START, mt_pure_function);
    TEST(VL_MT_START, mt_safe_postinit_function);
    TEST(VL_MT_START, mt_safe_excludes_function);
};

class bad {
    // pure functions can only call another pure function
    TEST(VL_PURE, no_attributes_function);
    TEST(VL_PURE, mt_unsafe_function);
    TEST(VL_PURE, mt_unsafe_one_function);
    TEST(VL_PURE, mt_safe_function);
    TEST(VL_PURE, mt_safe_postinit_function);
    TEST(VL_PURE, mt_safe_excludes_function);
    TEST(VL_PURE, mt_start_function);
    // mt_safe can call other mt_safe function, or
    // pure function
    TEST(VL_MT_SAFE, no_attributes_function);
    TEST(VL_MT_SAFE, mt_unsafe_function);
    TEST(VL_MT_SAFE, mt_unsafe_one_function);
    TEST(VL_MT_SAFE, mt_start_function);
    // mt_safe_postinit can call other mt_safe function, or
    // pure function
    TEST(VL_MT_SAFE_POSTINIT, no_attributes_function);
    TEST(VL_MT_SAFE_POSTINIT, mt_unsafe_function);
    TEST(VL_MT_SAFE_POSTINIT, mt_unsafe_one_function);
    TEST(VL_MT_SAFE_POSTINIT, mt_start_function);
    // mt_safe_excludes can call other mt_safe function, or
    // pure function
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, no_attributes_function);
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_unsafe_function);
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_unsafe_one_function);
    TEST2(VL_MT_SAFE_EXCLUDES, m_mutex, mt_start_function);
    // mt_start can call mt_safe function, or
    // pure function
    TEST(VL_MT_START, no_attributes_function);
    TEST(VL_MT_START, mt_unsafe_function);
    TEST(VL_MT_START, mt_unsafe_one_function);
    TEST(VL_MT_START, mt_start_function);
};
