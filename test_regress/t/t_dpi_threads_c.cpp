// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2018-2018 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include <atomic>
#include <cstdio>
#include <iostream>
#include <unistd.h>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# ifdef T_DPI_THREADS_COLLIDE
#  include "Vt_dpi_threads_collide__Dpi.h"
# else
#  include "Vt_dpi_threads__Dpi.h"
# endif
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
extern "C" {
    extern void dpii_sys_task();
    extern int dpii_failure();
}
#endif

//======================================================================

struct state {
    std::atomic<bool> task_is_running;
    std::atomic<int> failure;
    state()
        : task_is_running(false)
        , failure(false) {}
};

static state st;

void dpii_sys_task() {
    bool other_task_running = atomic_exchange(&st.task_is_running, true);
    if (other_task_running) {
        // Another task is running. This is a collision.
        st.failure = 1;
        std::cerr << "t_dpi_threads_c.cpp dpii_sys_task() saw threads collide.\n";
    } else {
        std::cerr << "t_dpi_threads_c.cpp dpii_sys_task() no collision. @" << &st.task_is_running << "\n";
    }

    // Spend some time in the DPI call, so that if we can have a collision
    // we probably will. Technically this is not guaranteed to detect every
    // race. However, one second is so much greater than the expected
    // runtime of everything else in the test, it really should pick up on
    // races just about all of the time.
    sleep(1);

    atomic_exchange(&st.task_is_running, false);
}

int dpii_failure() { return st.failure; }
