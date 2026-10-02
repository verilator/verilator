// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE
#include "TestCheck.h"
#include "vpi_user.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <string>
#include <vector>

int errors = 0;
int settleRuns = 0;

namespace {

vpiHandle find(const char* name) {
    vpiHandle handle = vpi_handle_by_name(const_cast<PLI_BYTE8*>(name), nullptr);
    TEST_CHECK_NZ_LABEL(name, handle);
    return handle;
}

uint32_t get(vpiHandle handle) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(handle, &value);
    return static_cast<uint32_t>(value.value.integer);
}

void put(vpiHandle handle, uint32_t v, PLI_INT32 flags) {
    s_vpi_value value{};
    value.format = vpiIntVal;
    value.value.integer = static_cast<PLI_INT32>(v);
    vpi_put_value(handle, &value, nullptr, flags);
}

void check(const char* label, uint32_t got, uint32_t exp) {
    if (got != exp) {
        std::printf("%%Error: %s: got 0x%02x exp 0x%02x\n", label, got, exp);
        ++errors;
    }
}

void accept(const char* name, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    vpiHandle const handle = find(name);
    if (!handle) return;
    put(handle, v, flags);
    s_vpi_error_info info{};
    if (vpi_chk_error(&info)) {
        std::printf("%%Error: %s: vpi error: %s\n", name, info.message);
        ++errors;
    }
    if (flags == vpiNoDelay) check(name, get(handle), v);
}

void reject(const char* name, uint32_t v, PLI_INT32 flags = vpiNoDelay) {
    vpiHandle const handle = find(name);
    if (!handle) return;
    const uint32_t before = get(handle);
    put(handle, v, flags);
    TEST_CHECK_ERROR(true);
    check(name, get(handle), before);
}

// A put into a masked signal writes the other bits and keeps the masked ones, silently; one
// changing only masked bits changes nothing, so leaves the model clean
void merge(const char* name, uint32_t v, uint32_t combMask) {
    vpiHandle const handle = find(name);
    if (!handle) return;
    const uint32_t before = get(handle);
    VerilatedVpi::clearEvalNeeded();
    put(handle, v, vpiNoDelay);
    TEST_CHECK_ERROR(false);
    const uint32_t exp = (v & ~combMask) | (before & combMask);
    check(name, get(handle), exp);
    TEST_CHECK_EQ_LABEL(name, VerilatedVpi::evalNeeded(), exp != before);
}

void putArray(const char* name, int index, const PLI_INT32* valsp, int num, bool expectError) {
    s_vpi_arrayvalue value{};
    value.format = vpiIntVal;
    value.value.integers = const_cast<PLI_INT32*>(valsp);
    PLI_INT32 indexes[1] = {index};
    vpi_put_value_array(find(name), &value, indexes, num);
    TEST_CHECK_ERROR(expectError);
}

// Flip each bit in turn, restoring any taken put: 'W' where a put changes it, 'r' where not
std::string writableBits(vpiHandle handle) {
    const int size = vpi_get(vpiSize, handle);
    if (size <= 0 || size > 32) return "?";
    std::string bits;
    for (int bit = size - 1; bit >= 0; --bit) {
        const uint32_t before = get(handle);
        put(handle, before ^ (1U << bit), vpiNoDelay);
        s_vpi_error_info info{};
        const bool refused = vpi_chk_error(&info) || get(handle) == before;
        if (!refused) put(handle, before, vpiNoDelay);
        bits += refused ? 'r' : 'W';
    }
    if (bits.find('r') == std::string::npos) return "W";
    if (bits.find('W') == std::string::npos) return "r";
    return bits;
}

void collect(vpiHandle scopep, std::vector<std::string>& linesr) {
    for (const PLI_INT32 type : {vpiReg, vpiNet}) {
        const vpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (const vpiHandle handle = vpi_scan(iterp)) {
            const std::string name = vpi_get_str(vpiFullName, handle);
            // A compiler temporary has no RTL name, and --public-flat-rw gives it no row.
            // Force controls are the exception, as V3Force makes them public.
            const bool forceCtl = name.find("__VforceEn") != std::string::npos
                                  || name.find("__VforceVal") != std::string::npos;
            if (!forceCtl && name.find("__") != std::string::npos) {
                std::printf("%%Error: compiler temporary is VPI-visible: %s\n", name.c_str());
                ++errors;
            }
            linesr.push_back(name + " " + writableBits(handle));
        }
    }
    for (const PLI_INT32 type : {vpiRegArray, vpiNetArray}) {
        const vpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (const vpiHandle arrayp = vpi_scan(iterp)) {
            const vpiHandle elemIterp = vpi_iterate(type == vpiRegArray ? vpiReg : vpiNet, arrayp);
            if (!elemIterp) continue;
            while (const vpiHandle handle = vpi_scan(elemIterp)) {
                linesr.push_back(std::string{vpi_get_str(vpiFullName, handle)} + " "
                                 + writableBits(handle));
            }
        }
    }
    for (const PLI_INT32 type : {vpiModule, vpiInterface}) {
        const vpiHandle iterp = vpi_iterate(type, scopep);
        if (!iterp) continue;
        while (const vpiHandle subp = vpi_scan(iterp)) collect(subp, linesr);
    }
}

struct ValueCb final {
    const char* name;
    vpiHandle handle;
    vpiHandle cb;
    uint32_t pre;
    int count;
    uint32_t value;
};

PLI_INT32 valueCb(p_cb_data cbp) {
    ValueCb* const vcp = reinterpret_cast<ValueCb*>(cbp->user_data);
    ++vcp->count;
    vcp->value = static_cast<uint32_t>(cbp->value->value.integer);
    return 0;
}

void armValueCb(ValueCb& vc) {
    vc.handle = find(vc.name);
    if (!vc.handle) return;
    vc.pre = get(vc.handle);
    static s_vpi_value value{};
    value.format = vpiIntVal;
    s_cb_data cb{};
    cb.reason = cbValueChange;
    cb.cb_rtn = valueCb;
    cb.obj = vc.handle;
    cb.value = &value;
    cb.user_data = reinterpret_cast<PLI_BYTE8*>(&vc);
    vc.cb = vpi_register_cb(&cb);
    TEST_CHECK_NZ_LABEL(vc.name, vc.cb);
}

}  // namespace

// Called from an initial block: each read is from the same eval, after its input moved
void midEvalRead(int src) {
    const uint32_t got = get(find("t.mid_c"));
    std::printf("mid-eval t.mid_c 0x%02x\n", got);
    check("t.mid_c mid-eval", got, (static_cast<uint32_t>(src) + 1) & 0xff);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->fatalOnVpiError(false);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), ""}};

    const auto cycle = [&]() {
        topp->clk = 1;
        topp->eval();
        topp->clk = 0;
        topp->eval();
    };

    topp->clk = 0;
    topp->rst = 1;
    topp->rst_n = 0;
    topp->set_n = 0;
    topp->ld = 1;
    topp->en = 0;
    topp->never = 0;
    topp->sel = 1;
    topp->d = 0x21;
    topp->in_a = 0x40;
    // Armed before the first eval, as from vlog_startup_routines: each fires for its settle
    std::vector<ValueCb> valueCbs;
    for (const char* name :
         {"t.ch1", "t.fmid_c", "t.sib_b", "t.al_sw", "t.cy0.din", "t.cy0.cy", "t.cy1.cy",
          "t.ifd.din", "t.ifd.a", "t.ff_q", "t.hl_c", "t.u_sub.i"}) {
        valueCbs.push_back({name, nullptr, nullptr, 0, 0, 0});
    }
    for (ValueCb& vc : valueCbs) armValueCb(vc);
    topp->eval();
    VerilatedVpi::callValueCbs();
    for (ValueCb& vc : valueCbs) {
        std::printf("cbValueChange %s pre 0x%02x fired %d 0x%02x\n", vc.name, vc.pre, vc.count,
                    vc.value);
        if (vc.cb) vpi_remove_cb(vc.cb);
    }
    topp->rst = 0;
    topp->rst_n = 1;
    topp->set_n = 1;
    topp->ld = 0;
    cycle();
    cycle();

    // Before either instance's own row refreshes it, so a refresh of the wrong one shows
    for (const char* name : {"t.fyx0_c", "t.fyx1_c"}) {
        const std::string inst = std::string{"t.fy"} + name[5];
        check(name, get(find(name)), 0xff & ((get(find((inst + ".r").c_str())) + 1) ^ 0x55));
    }

    // Each cone reads storage only a compiler temporary holds
    check("t.px_o", get(find("t.px_o")), 0xff & ~(0x21 ^ 0x40));
    check("t.u_px.i", get(find("t.u_px.i")), 0x21 ^ 0x40);
    check("t.nest_c", get(find("t.nest_c")), (0x21 + 3) ^ (0x40 + 3));
    check("t.tw weak", get(find("t.tw")), 0x40);
    check("t.tw_r weak", get(find("t.tw_r")), 0x40);
    topp->en = 1;
    topp->eval();
    check("t.tw_r strong", get(find("t.tw_r")), 0x21);
    topp->en = 0;
    topp->eval();

    // The scope API has no storage to return for a computed signal
    if (const VerilatedScope* const scopep = contextp->scopeFind("t")) {
        const VerilatedVar* const conep = scopep->varFind("px_o");
        const VerilatedVar* const storedp = scopep->varFind("ff_q");
        check("t.px_o datap", conep && !conep->datap(), 1);
        check("t.ff_q datap", storedp && storedp->datap(), 1);
    } else {
        check("t scope", 0, 1);
    }

    for (const char* name :
         {"t.ff_q", "t.arn_q", "t.arp_q", "t.as_q", "t.al_q", "t.lat_q", "t.ilat_q",
          "t.undr_mem[2]", "t.init_r", "t.ini_r", "t.in_a", "t.frw_c", "t.frc_al", "t.u_ff.q",
          "t.bus.q", "t.pf", "t.intf_inst.sig", "t.spl_l", "t.imp_l"}) {
        accept(name, 0x5a);
    }
    // Each instance as the RTL drives it, beside a comb-driven instance of the same variable
    for (const char* name : {"t.ia.q", "t.cf0.p", "t.cu.p", "t.mc2.m"}) accept(name, 0x5a);
    const uint32_t mix = get(find("t.u_mix.m"));
    accept("t.u_mix.m", (mix & 1) | 0xa4);
    // A flop holds the put until its next edge
    topp->d = 0x33;
    topp->eval();
    check("t.ff_q held", get(find("t.ff_q")), 0x5a);
    check("t.lat_q held", get(find("t.lat_q")), 0x5a);
    check("t.ib.q follows", get(find("t.ib.q")), 0x5a);
    cycle();
    check("t.ff_q edge", get(find("t.ff_q")), 0x33);
    // The put is in the storage the logic reads
    check("t.n_ff", get(find("t.n_ff")), 0x5a);
    check("t.n_mix", get(find("t.n_mix")), (mix & 1) | 0xa4);
    check("t.n_if", get(find("t.n_if")), 0x5a);
    check("t.n_in", get(find("t.n_in")), 0xa5);
    check("t.n_cons", get(find("t.n_cons")), 0x5a);
    check("t.n_ia", get(find("t.n_ia")), 0x5a);
    check("t.n_cf0", get(find("t.n_cf0")), 0x5a);
    check("t.n_cu", get(find("t.n_cu")), 0x5a);
    check("t.n_mc2", get(find("t.n_mc2")), 0x5a);
    check("t.ia.q edge", get(find("t.ia.q")), 0x33);
    check("t.ib.q edge", get(find("t.ib.q")), 0x33);

    for (const char* name :
         {"t.asg_w",  "t.ac_c",    "t.star_c", "t.out_c",  "t.sub_o",   "t.u_sub.o", "t.fc_c",
          "t.gclk",   "t.vidx[0]", "t.cst_w",  "t.loop_c", "t.while_c", "t.w_ff",    "t.w_mix",
          "t.u_in.i", "t.c1_c",    "t.cg_c",   "t.pon_c",  "t.pand_c",  "t.px_o",    "t.u_px.i",
          "t.u_px.o", "t.tw",      "t.tw_r",   "t.out_q",  "t.out_m"}) {
        reject(name, get(find(name)) ^ 0x5b);
    }
    for (const char* name : {"t.ib.q", "t.cf1.p"}) reject(name, get(find(name)) ^ 0x5b);
    for (const char* name :
         {"t.ch2",    "t.sgn_c",    "t.cat_c",     "t.self_c",   "t.part_c",  "t.ctv_c",
          "t.cts_c",  "t.hl_c",     "t.us_c.a",    "t.mem_c[0]", "t.mixf_w",  "t.ovl_w",
          "t.al1",    "t.al2",      "t.pass_o",    "t.fmid_c",   "t.sib_b",   "t.sib_c",
          "t.wd_w",   "t.u_wdrv.o", "t.rdpin",     "t.ivec",     "t.cy0.din", "t.cy1.din",
          "t.cy0.cy", "t.tmp_o",    "t.u_tmp.cpy", "t.ifd.a",    "t.alc_x"}) {
        reject(name, get(find(name)) ^ 0x5b);
    }
    {
        vpiHandle const mdp = vpi_handle_by_index(vpi_handle_by_index(find("t.mdp_c"), 0), 0);
        TEST_CHECK_NZ_LABEL("t.mdp_c[0][0]", mdp);
        if (mdp) {
            const uint32_t before = get(mdp);
            put(mdp, before ^ 0x5b, vpiNoDelay);
            TEST_CHECK_ERROR(true);
            check("t.mdp_c[0][0]", get(mdp), before);
        }
    }
    // A refused put into one instance leaves the other's value as its own driver made it
    check("t.cy1.cy", get(find("t.cy1.cy")), get(find("t.k_q")) ^ 0xa5);
    // Each alias row reports its own metadata, not its canonical's, and reads the canonical
    for (const char* name : {"t.al_sw", "t.al_nw", "t.al1", "t.sib_bt", "t.ch1"}) {
        TEST_CHECK_EQ_LABEL(name, vpi_get(vpiSize, find(name)), 8);
    }
    TEST_CHECK_EQ_LABEL("t.al_sw", vpi_get(vpiSigned, find("t.al_sw")), 1);
    TEST_CHECK_EQ_LABEL("t.sgn_c", vpi_get(vpiSigned, find("t.sgn_c")), 1);
    TEST_CHECK_EQ_LABEL("t.sib_bt", vpi_get(vpiType, find("t.sib_bt")), vpiBitVar);
    TEST_CHECK_EQ_LABEL("t.ch1", vpi_get(vpiType, find("t.ch1")), vpiReg);
    TEST_CHECK_EQ_LABEL("t.al1", vpi_get(vpiSigned, find("t.al1")), 0);
    TEST_CHECK_EQ_LABEL("t.al_sw", get(vpi_handle(vpiLeftRange, find("t.al_sw"))), 8);
    TEST_CHECK_EQ_LABEL("t.al_sw", get(vpi_handle(vpiRightRange, find("t.al_sw"))), 1);
    TEST_CHECK_EQ_LABEL("t.pk_al", vpi_get(vpiSize, find("t.pk_al")), 16);
    for (const char* name : {"t.al_sw", "t.al_nw"})
        check(name, get(find(name)), get(find("t.k_q")));
    check("t.sib_bt", get(find("t.sib_bt")), get(find("t.ch1")));
    check("t.pk_al", get(find("t.pk_al")), get(find("t.pk_c")));
    check("t.us_c.b", get(find("t.us_c.b")), 0xff & ~get(find("t.us_c.a")));
    // Only the bits no comb driver writes take a put
    const uint32_t nopre = get(find("t.nopre_c"));
    accept("t.nopre_c", nopre ^ 0xa0);
    merge("t.nopre_c", get(find("t.nopre_c")) ^ 0x1, 0x0f);
    merge("t.nopre_c", get(find("t.nopre_c")) ^ 0xff, 0x0f);
    accept("t.pla_l", get(find("t.pla_l")) ^ 0x0f);
    accept("t.plb_l", get(find("t.plb_l")) ^ 0x0f);
    merge("t.plb_l", get(find("t.plb_l")) ^ 0xf0, 0xf0);
    accept("t.plc_l", get(find("t.plc_l")) ^ 0x0c);
    merge("t.plc_l", get(find("t.plc_l")) ^ 0x03, 0x03);
    merge("t.plc_l", get(find("t.plc_l")) ^ 0xff, 0x03);
    reject("t.plv_c", get(find("t.plv_c")) ^ 0x01);
    accept("t.plm_l[0]", get(find("t.plm_l[0]")) ^ 0xff);
    merge("t.plm_l[1]", get(find("t.plm_l[1]")) ^ 0xff, 0xff);
    merge("t.ple_l[1]", get(find("t.ple_l[1]")) ^ 0xff, 0x0f);
    merge("t.ple_l[1]", get(find("t.ple_l[1]")) ^ 0x0f, 0x0f);
    merge("t.plu_l[0]", get(find("t.plu_l[0]")) ^ 0xff, 0xf0);
    merge("t.plu_l[1]", get(find("t.plu_l[1]")) ^ 0xff, 0x0f);
    reject("t.ac_c", 0, vpiInertialDelay);
    reject("t.ac_c", 0, vpiForceFlag);
    // public_flat_rw takes a put on a comb-driven net until the next eval
    for (const char* name : {"t.u_na.z", "t.u_na.w"}) accept(name, 0x5a);
    reject("t.u_na.q", get(find("t.u_na.q")) ^ 0x5b);

    // A put may change only the bits no comb driver writes
    const uint32_t st = get(find("t.st"));
    accept("t.st", (st & 1) | (0x05 << 1));
    merge("t.st", get(find("t.st")) ^ 1, 0x01);
    {
        // An inertial put is merged when it lands
        const uint32_t before = get(find("t.st"));
        accept("t.st", before ^ 0xff, vpiInertialDelay);
        VerilatedVpi::doInertialPuts();
        check("t.st inertial merged", get(find("t.st")), before ^ 0xfe);
    }
    accept("t.st", (st & 1) | (0x09 << 1), vpiInertialDelay);
    VerilatedVpi::doInertialPuts();
    check("t.st inertial", get(find("t.st")), (st & 1) | (0x09 << 1));
    // A mixed-mask signal is not forceable, so force/release are refused as-is
    reject("t.st", get(find("t.st")) ^ (1 << 1), vpiForceFlag);
    reject("t.st", get(find("t.st")) ^ (1 << 1), vpiReleaseFlag);
    {
        // A non-canonical inertial-delay format falls through to the ordinary put and is refused
        vpiHandle const handle = find("t.st");
        const uint32_t before = get(handle);
        s_vpi_value value{};
        value.format = vpiTimeVal;
        vpi_put_value(handle, &value, nullptr, vpiInertialDelay);
        TEST_CHECK_ERROR(true);
        check("t.st inertial bad format", get(handle), before);
    }
    const uint32_t vec = get(find("t.vec"));
    accept("t.vec", (vec & 1) | 0xa4);
    merge("t.vec", get(find("t.vec")) ^ 1, 0x01);
    merge("t.u_mix.m", get(find("t.u_mix.m")) ^ 1, 0x01);
    accept("t.pmem[0]", 0x5a);
    accept("t.pmem[2]", 0x5b);
    merge("t.pmem[1]", get(find("t.pmem[1]")) ^ 0x5a, 0xff);
    merge("t.pmem[3]", get(find("t.pmem[3]")) ^ 0x5a, 0xff);
    // Instances of one variable, each masked by its own comb drivers
    for (const auto& pr : {std::make_pair("t.cp.p", 0x0fU), std::make_pair("t.mc0.m", 0x0fU),
                           std::make_pair("t.mc1.m", 0xf0U)}) {
        const uint32_t v = get(find(pr.first));
        accept(pr.first, v ^ (0xffU & ~pr.second));
        merge(pr.first, get(find(pr.first)) ^ pr.second, pr.second);
        merge(pr.first, get(find(pr.first)) ^ 0xff, pr.second);
    }

    const PLI_INT32 one[1] = {0x6c};
    putArray("t.pmem", 0, one, 1, false);
    check("t.pmem[0] array", get(find("t.pmem[0]")), 0x6c);
    const PLI_INT32 two[2] = {0x7d, static_cast<PLI_INT32>(get(find("t.pmem[1]")) ^ 0xff)};
    const uint32_t pmem1 = get(find("t.pmem[1]"));
    putArray("t.pmem", 0, two, 2, false);
    check("t.pmem[0] array merged", get(find("t.pmem[0]")), 0x7d);
    check("t.pmem[1] array merged", get(find("t.pmem[1]")), pmem1);
    const PLI_INT32 masked[1] = {static_cast<PLI_INT32>(pmem1 ^ 0xff)};
    putArray("t.pmem", 1, masked, 1, false);
    check("t.pmem[1] array kept", get(find("t.pmem[1]")), pmem1);
    putArray("t.vidx", 0, one, 1, true);

    // 4 array dims exceed VPI_TABLE_MAX_DIMS: no per-bit mask, so the whole variable
    // is refused, including the element the partial assign never touches
    reject("t.m4[0][0]", get(find("t.m4[0][0]")) ^ 0xf0);
    reject("t.m4[1][1]", get(find("t.m4[1][1]")) ^ 0xff);

    // A refused put into a retained comb signal leaves the flop sampling it its driven value
    {
        const uint32_t driven = get(find("t.ret_c"));
        reject("t.ret_c", driven ^ 0x5b);
        cycle();
        check("t.ret_q", get(find("t.ret_q")), driven);
        check("t.ret_c edge", get(find("t.ret_c")), get(find("t.k_q")) ^ 0x5a);
    }

    // An unparsable decimal put writes nothing, so leaves nothing to re-settle
    {
        vpiHandle const handle = find("t.ff_q");
        topp->eval();
        const int runs = settleRuns;
        const uint32_t before = get(handle);
        s_vpi_value value{};
        value.format = vpiDecStrVal;
        value.value.str = const_cast<PLI_BYTE8*>("A123");
        vpi_put_value(handle, &value, nullptr, vpiNoDelay);
        TEST_CHECK_ERROR(true);
        topp->eval();
        check("t.ff_q bad decimal", get(handle), before);
        TEST_CHECK_EQ_LABEL("t.ff_q bad decimal settles", settleRuns, runs + 1);
        const std::string dec = std::to_string(before);
        value.value.str = const_cast<PLI_BYTE8*>(dec.c_str());
        vpi_put_value(handle, &value, nullptr, vpiNoDelay);
        TEST_CHECK_ERROR(false);
        topp->eval();
        TEST_CHECK_EQ_LABEL("t.ff_q decimal settles", settleRuns, runs + 3);
    }

    // The whole VPI-visible set and its writability, which no optimisation flag may change
    std::vector<std::string> lines;
    collect(nullptr, lines);
    std::sort(lines.begin(), lines.end());
    for (const std::string& line : lines) std::printf("%s\n", line.c_str());

    topp->final();
    if (!errors) std::printf("*-* All Finished *-*\n");
    return errors ? 10 : 0;
}
