// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Toru Niina
// SPDX-License-Identifier: CC0-1.0

#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void tb_sv_wait(int n);

int tb_c_wait() {
    tb_sv_wait(10);
    return 0;
}

#ifdef __cplusplus
}

#endif
