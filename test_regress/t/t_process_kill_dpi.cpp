// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include <svdpi.h>

extern "C" void kill_from_export(svBit self);

extern "C" int call_kill(svBit self) {
    kill_from_export(self);
    return 42;
}

extern "C" int call_kill_task() {
    kill_from_export(1);
    return svIsDisabledState();
}
