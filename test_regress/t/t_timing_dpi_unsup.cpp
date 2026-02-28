// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Toru Niina
// SPDX-License-Identifier: CC0-1.0

#include "Vt_timing_dpi__Dpi.h"

int tb_c_wait() {
    tb_sv_wait(10);
    return 0;
}
