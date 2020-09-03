// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

//======================================================================

class TestVpiHandle {
    /// For testing, etc, wrap vpiHandle in an auto-releasing class
    vpiHandle m_handle;
    bool m_free;

public:
    TestVpiHandle()
        : m_handle(NULL)
        , m_free(true) {}
    TestVpiHandle(vpiHandle h)
        : m_handle(h)
        , m_free(true) {}
    ~TestVpiHandle() {
        if (m_handle && m_free) {
            { vpi_free_object(m_handle); m_handle = NULL; }
        }
    }
    operator vpiHandle() const { return m_handle; }
    inline TestVpiHandle& operator=(vpiHandle h) {
        m_handle = h;
        return *this;
    }
    TestVpiHandle& nofree() {
        m_free = false;
        return *this;
    }
};
