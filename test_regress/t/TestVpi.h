// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

// Avoid C++11 in this file as not all simulators allow it

//======================================================================

class TestVpiHandle {
    /// For testing, etc, wrap vpiHandle in an auto-releasing class
    vpiHandle m_handle;  // No = as no C++11
    bool m_freeit;  // No = as no C++11

public:
    TestVpiHandle()
        : m_handle(NULL)
        , m_freeit(true) {}
    TestVpiHandle(vpiHandle h)
        : m_handle(h)
        , m_freeit(true) {}
    ~TestVpiHandle() { release(); }
    operator vpiHandle() const { return m_handle; }
    inline TestVpiHandle& operator=(vpiHandle h) {
        release();
        m_handle = h;
        return *this;
    }
    void release() {
        if (m_handle && m_freeit) {
            // Below not VL_DO_DANGLING so is portable
#ifdef IVERILOG
            vpi_free_object(m_handle);
#else
            vpi_release_handle(m_handle);
#endif
            m_handle = NULL;
        }
    }
    // Freed by another action e.g. vpi_scan; so empty and don't free again
    void freed() {
        m_handle = NULL;
        m_freeit = false;
    }
};
