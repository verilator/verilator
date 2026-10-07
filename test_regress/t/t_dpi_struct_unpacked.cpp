// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "svdpi.h"

#include <cstdio>
#include <cstring>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

// A structure may be declared by the user, instead of by the DPI header
#define VL_DPITYPE_inner_t_
typedef struct {
    int x;
    svBitVecVal v[3][SV_PACKED_DATA_NELEMS(33)];
    struct {
        char a;
        short m[2][3];
    } anon;
} inner_t;

#include VM_PREFIX_INCLUDE_DPI

int errors = 0;
int dpii_failure() { return errors; }

// String for 'n', kept until SystemVerilog copies it after the call
static const char* str(int n) {
    static char s_bufs[8][16];
    static int s_next = 0;
    char* const bufp = s_bufs[s_next++ % 8];
    snprintf(bufp, sizeof(s_bufs[0]), "s%d", n);
    return bufp;
}

static int s_target;  // Pointed to by the chandles made here, SystemVerilog makes them null

// Values from 'n', as SystemVerilog makes them
static void fillBasic(basic_t* p, int n) {
    p->b = static_cast<char>(-1 - n);
    p->bu = static_cast<unsigned char>(200 + n);
    p->si = static_cast<short>(-1000 - n);
    p->i = -100000 - n;
    p->iu = 0xf0000000U + n;
    p->li = -5000000000LL - n;
    p->liu = 0xf000000000000000ULL + n;
    p->r = 1.5 + n;
    p->ch = &s_target;
    p->s = str(n);
    p->bt = n & 1;
    p->lg = !(n & 1);
    p->bv7[0] = (0x55 ^ n) & 0x7f;
    p->lv65[0] = {static_cast<svBitVecVal>(n), 0};
    p->lv65[1] = {0xdeadbeef, 0};
    p->lv65[2] = {1, 0};
    p->bv96[0] = 0x9abcdef0;
    p->bv96[1] = n;
    p->bv96[2] = 0x12345678;
    p->ig[0] = {static_cast<svBitVecVal>(-7 - n), 0};
    p->tm[0] = {0x89abcdef, 0};
    p->tm[1] = {static_cast<svBitVecVal>(n), 0};
    p->en[0] = (n & 1) ? 6 : 1;
    p->pk[0] = {static_cast<svBitVecVal>((((n + 3) & 0xf) << 3) | (n & 7)), 0};
    p->pa[0] = ((n & 0xff) << 8) | 0xa5;
    p->lt[0] = {static_cast<svBitVecVal>((n + 9) & 0x7f), 0};
}
static void checkBasic(const basic_t* p, int n) {
    basic_t e;
    fillBasic(&e, n);
    TEST_CHECK_EQ(p->b, e.b);
    TEST_CHECK_EQ(p->bu, e.bu);
    TEST_CHECK_EQ(p->si, e.si);
    TEST_CHECK_EQ(p->i, e.i);
    TEST_CHECK_EQ(p->iu, e.iu);
    TEST_CHECK_EQ(p->li, e.li);
    TEST_CHECK_EQ(p->liu, e.liu);
    TEST_CHECK_EQ(p->r, e.r);
    TEST_CHECK_Z(p->ch);
    TEST_CHECK_CSTR(p->s, e.s);
    TEST_CHECK_EQ(p->bt, e.bt);
    TEST_CHECK_EQ(p->lg, e.lg);
    TEST_CHECK_EQ(std::memcmp(p->bv7, e.bv7, sizeof(e.bv7)), 0);
    TEST_CHECK_EQ(std::memcmp(p->lv65, e.lv65, sizeof(e.lv65)), 0);
    TEST_CHECK_EQ(std::memcmp(p->bv96, e.bv96, sizeof(e.bv96)), 0);
    TEST_CHECK_EQ(std::memcmp(p->ig, e.ig, sizeof(e.ig)), 0);
    TEST_CHECK_EQ(std::memcmp(p->tm, e.tm, sizeof(e.tm)), 0);
    TEST_CHECK_EQ(std::memcmp(p->en, e.en, sizeof(e.en)), 0);
    TEST_CHECK_EQ(std::memcmp(p->pk, e.pk, sizeof(e.pk)), 0);
    TEST_CHECK_EQ(std::memcmp(p->pa, e.pa, sizeof(e.pa)), 0);
    TEST_CHECK_EQ(std::memcmp(p->lt, e.lt, sizeof(e.lt)), 0);
}

static void fillInner(inner_t* p, int n) {
    p->x = 1000 * n + 7;
    for (int k = 0; k < 3; ++k) {
        p->v[k][0] = 16 * n + k + 1;
        p->v[k][1] = 1;
    }
    p->anon.a = static_cast<char>(n + 100);
    for (int r = 0; r < 2; ++r) {
        for (int c = 0; c < 3; ++c)
            p->anon.m[r][c] = static_cast<short>(100 * n + 10 * (r + 1) + c);
    }
}
static void checkInner(const inner_t* p, int n) {
    inner_t e;
    fillInner(&e, n);
    TEST_CHECK_EQ(p->x, e.x);
    TEST_CHECK_EQ(std::memcmp(p->v, e.v, sizeof(e.v)), 0);
    TEST_CHECK_EQ(p->anon.a, e.anon.a);
    TEST_CHECK_EQ(std::memcmp(p->anon.m, e.anon.m, sizeof(e.anon.m)), 0);
}

static void fillOuter(outer_t* p, int n) {
    fillBasic(&p->basic, n);
    for (int k = 0; k < 2; ++k) fillInner(&p->inner[k], n + k);
}
static void checkOuter(const outer_t* p, int n) {
    checkBasic(&p->basic, n);
    for (int k = 0; k < 2; ++k) checkInner(&p->inner[k], n + k);
}

int dpii_basic(const basic_t* i, basic_t* o, basic_t* io) {
    static int n = 0;
    checkBasic(i, n);
    checkBasic(io, n + 1);
    fillBasic(o, n + 2);
    fillBasic(io, n + 3);
    n += 10;
    return 0;
}

void dpii_outer(const outer_t* i, outer_t* o, outer_t* io) {
    static int n = 0;
    checkOuter(i, n);
    checkOuter(io, n + 1);
    fillOuter(o, n + 2);
    fillOuter(io, n + 3);
    n += 10;
}

// Unpacked arrays are C arrays of the elements, the lowest index first
void dpii_array(const inner_t* i, inner_t* o, inner_t* io) {
    static int n = 0;
    for (int k = 0; k < 6; ++k) checkInner(&i[k], n + k);
    for (int k = 0; k < 2; ++k) checkInner(&io[k], n + 6 + k);
    for (int k = 0; k < 3; ++k) fillInner(&o[k], n + 8 + k);
    for (int k = 0; k < 2; ++k) fillInner(&io[k], n + 11 + k);
    n += 10;
}

void dpii_check_export(int n) {
    outer_t i;
    outer_t o;
    outer_t io;
    fillOuter(&i, n);
    fillOuter(&io, n + 1);
    dpix_outer(&i, &o, &io);
    checkOuter(&o, n + 2);
    checkOuter(&io, n + 3);

    const eval ai[2] = {{n}, {n + 1}};
    eval ao[2];
    dpix_array(ai, ao);
    for (int k = 0; k < 2; ++k) TEST_CHECK_EQ(ao[k].x, n + k + 1);
}

int dpii_sub(const sub_t* i) { return i->w + 1; }
