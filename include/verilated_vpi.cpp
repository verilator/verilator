// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2009-2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilated VPI implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use the VPI.
///
/// Use "verilator --vpi" to add this to the Makefile for the linker.
///
/// For documentation on the exported functions (named vpi_*) that are
/// implemented here, refer to the IEEE DPI chapter.
///
//=========================================================================

#define VERILATOR_VERILATED_VPI_CPP_

#include "verilated_vpi.h"

#include "verilated.h"
#include "verilated_imp.h"

#include <list>
#include <map>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

//======================================================================
// Internal constants

#define VL_DEBUG_IF_PLI VL_DEBUG_IF
constexpr unsigned VL_VPI_LINE_SIZE_ = 8192;

//======================================================================
// Internal macros

#define VL_VPI_INTERNAL_ VerilatedVpiImp::error_info()->setMessage(vpiInternal)->setMessage
#define VL_VPI_SYSTEM_ VerilatedVpiImp::error_info()->setMessage(vpiSystem)->setMessage
#define VL_VPI_ERROR_ VerilatedVpiImp::error_info()->setMessage(vpiError)->setMessage
#define VL_VPI_WARNING_ VerilatedVpiImp::error_info()->setMessage(vpiWarning)->setMessage
#define VL_VPI_NOTICE_ VerilatedVpiImp::error_info()->setMessage(vpiNotice)->setMessage
#define VL_VPI_ERROR_RESET_ VerilatedVpiImp::error_info()->resetError

// Not supported yet
#define VL_VPI_UNIMP_() \
    (VL_VPI_ERROR_(__FILE__, __LINE__, Verilated::catName("Unsupported VPI function: ", __func__)))

//======================================================================
// Implementation

// Base VPI handled object
class VerilatedVpio VL_NOT_FINAL {
    // CONSTANTS
    // Magic value stored in front of object to detect double free etc
    // Must be odd, as aligned pointer can never be odd
    static constexpr uint32_t activeMagic() { return 0xfeed100f; }

    // MEM MANGLEMENT
    // Internal note: Globals may multi-construct, see verilated.cpp top.
    static VL_THREAD_LOCAL uint8_t* t_freeHead;

public:
    // CONSTRUCTORS
    VerilatedVpio() = default;
    virtual ~VerilatedVpio() = default;
    static void* operator new(size_t size) VL_MT_SAFE {
        // We new and delete tons of vpi structures, so keep them around
        // To simplify our free list, we use a size large enough for all derived types
        // We reserve word zero for the next pointer, as that's safer in case a
        // dangling reference to the original remains around.
        static constexpr size_t CHUNK_SIZE = 96;
        if (VL_UNCOVERABLE(size > CHUNK_SIZE))
            VL_FATAL_MT(__FILE__, __LINE__, "", "increase CHUNK_SIZE");
        if (VL_LIKELY(t_freeHead)) {
            uint8_t* const newp = t_freeHead;
            t_freeHead = *(reinterpret_cast<uint8_t**>(newp));
            *(reinterpret_cast<uint32_t*>(newp)) = activeMagic();
            return newp + 8;
        }
        // +8: 8 bytes for next
        uint8_t* newp = reinterpret_cast<uint8_t*>(::operator new(CHUNK_SIZE + 8));
        *(reinterpret_cast<uint32_t*>(newp)) = activeMagic();
        return newp + 8;
    }
    static void operator delete(void* obj, size_t /*size*/)VL_MT_SAFE {
        uint8_t* const oldp = (static_cast<uint8_t*>(obj)) - 8;
        if (VL_UNLIKELY(*(reinterpret_cast<uint32_t*>(oldp)) != activeMagic())) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "vpi_release_handle() called on same object twice, or on non-Verilator "
                        "VPI object");
        }
#ifdef VL_VPI_IMMEDIATE_FREE  // Define to aid in finding leaky handles
        ::operator delete(oldp);
#else
        *(reinterpret_cast<void**>(oldp)) = t_freeHead;
        t_freeHead = oldp;
#endif
    }
    // MEMBERS
    static VerilatedVpio* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpio*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    inline vpiHandle castVpiHandle() { return reinterpret_cast<vpiHandle>(this); }
    // ACCESSORS
    virtual const char* name() const { return "<null>"; }
    virtual const char* fullname() const { return "<null>"; }
    virtual const char* defname() const { return "<null>"; }
    virtual uint32_t type() const { return 0; }
    virtual uint32_t size() const { return 0; }
    virtual const VerilatedRange* rangep() const { return nullptr; }
    virtual vpiHandle dovpi_scan() { return nullptr; }
    virtual PLI_INT32 dovpi_remove_cb() { return 0; }
};

class VerilatedVpioTimedCb final : public VerilatedVpio {
    // A handle to a timed callback created with vpi_register_cb
    // User can call vpi_remove_cb or vpi_release_handle on it
    const uint64_t m_id;  // Unique id/sequence number to find schedule's event
    const QData m_time;

public:
    VerilatedVpioTimedCb(uint64_t id, QData time)
        : m_id{id}
        , m_time{time} {}
    ~VerilatedVpioTimedCb() override = default;
    static VerilatedVpioTimedCb* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioTimedCb*>(reinterpret_cast<VerilatedVpioTimedCb*>(h));
    }
    uint32_t type() const override { return vpiCallback; }
    PLI_INT32 dovpi_remove_cb() override;
};

class VerilatedVpioReasonCb final : public VerilatedVpio {
    // A handle to a non-timed callback created with vpi_register_cb
    // User can call vpi_remove_cb or vpi_release_handle on it
    const uint64_t m_id;  // Unique id/sequence number to find schedule's event
    const PLI_INT32 m_reason;  // VPI callback reason code

public:
    // cppcheck-suppress uninitVar  // m_value
    VerilatedVpioReasonCb(uint64_t id, PLI_INT32 reason)
        : m_id{id}
        , m_reason{reason} {}
    ~VerilatedVpioReasonCb() override = default;
    static VerilatedVpioReasonCb* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioReasonCb*>(reinterpret_cast<VerilatedVpioReasonCb*>(h));
    }
    uint32_t type() const override { return vpiCallback; }
    PLI_INT32 dovpi_remove_cb() override;
};

class VerilatedVpioConst final : public VerilatedVpio {
    const int32_t m_num;

public:
    explicit VerilatedVpioConst(int32_t num)
        : m_num{num} {}
    ~VerilatedVpioConst() override = default;
    static VerilatedVpioConst* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioConst*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiConstant; }
    int32_t num() const { return m_num; }
};

class VerilatedVpioVarBase VL_NOT_FINAL : public VerilatedVpio {
protected:
    const VerilatedVar* m_varp = nullptr;
    const VerilatedScope* m_scopep = nullptr;
    const VerilatedRange& get_range() const {
        // Determine number of dimensions and return outermost
        return (m_varp->dims() > 1) ? m_varp->unpacked() : m_varp->packed();
    }

public:
    VerilatedVpioVarBase(const VerilatedVar* varp, const VerilatedScope* scopep)
        : m_varp{varp}
        , m_scopep{scopep} {}
    explicit VerilatedVpioVarBase(const VerilatedVpioVarBase* varp) {
        if (varp) {
            m_varp = varp->m_varp;
            m_scopep = varp->m_scopep;
        }
    }
    static VerilatedVpioVarBase* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVarBase*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    const VerilatedVar* varp() const { return m_varp; }
    const VerilatedScope* scopep() const { return m_scopep; }
    uint32_t size() const override { return get_range().elements(); }
    const VerilatedRange* rangep() const override { return &get_range(); }
    const char* name() const override { return m_varp->name(); }
    const char* fullname() const override {
        static VL_THREAD_LOCAL std::string t_out;
        t_out = std::string{m_scopep->name()} + "." + name();
        return t_out.c_str();
    }
};

class VerilatedVpioParam final : public VerilatedVpioVarBase {
public:
    VerilatedVpioParam(const VerilatedVar* varp, const VerilatedScope* scopep)
        : VerilatedVpioVarBase{varp, scopep} {}
    ~VerilatedVpioParam() override = default;

    static VerilatedVpioParam* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioParam*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiParameter; }
    void* varDatap() const { return m_varp->datap(); }
};

class VerilatedVpioRange final : public VerilatedVpio {
    const VerilatedRange* const m_range;

public:
    explicit VerilatedVpioRange(const VerilatedRange* range)
        : m_range{range} {}
    ~VerilatedVpioRange() override = default;
    static VerilatedVpioRange* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioRange*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiRange; }
    uint32_t size() const override { return m_range->elements(); }
    const VerilatedRange* rangep() const override { return m_range; }
};

class VerilatedVpioRangeIter final : public VerilatedVpio {
    // Only supports 1 dimension
    const VerilatedRange* const m_range;
    bool m_done = false;

public:
    explicit VerilatedVpioRangeIter(const VerilatedRange* range)
        : m_range{range} {}
    ~VerilatedVpioRangeIter() override = default;
    static VerilatedVpioRangeIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioRangeIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiIterator; }
    vpiHandle dovpi_scan() override {
        if (VL_UNLIKELY(m_done)) {
            delete this;  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
            return nullptr;
        }
        m_done = true;
        return ((new VerilatedVpioRange{m_range})->castVpiHandle());
    }
};

class VerilatedVpioScope VL_NOT_FINAL : public VerilatedVpio {
protected:
    const VerilatedScope* const m_scopep;

public:
    explicit VerilatedVpioScope(const VerilatedScope* scopep)
        : m_scopep{scopep} {}
    ~VerilatedVpioScope() override = default;
    static VerilatedVpioScope* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioScope*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiScope; }
    const VerilatedScope* scopep() const { return m_scopep; }
    const char* name() const override { return m_scopep->name(); }
    const char* fullname() const override { return m_scopep->name(); }
};

class VerilatedVpioVar VL_NOT_FINAL : public VerilatedVpioVarBase {
    uint8_t* m_prevDatap = nullptr;  // Previous value of data, for cbValueChange
    union {
        uint8_t u8[4];
        uint32_t u32;
    } m_mask;  // memoized variable mask
    uint32_t m_entSize = 0;  // memoized variable size
protected:
    void* m_varDatap = nullptr;  // varp()->datap() adjusted for array entries
    int32_t m_index = 0;

public:
    VerilatedVpioVar(const VerilatedVar* varp, const VerilatedScope* scopep)
        : VerilatedVpioVarBase{varp, scopep} {
        m_mask.u32 = VL_MASK_I(varp->packed().elements());
        m_entSize = varp->entSize();
        m_varDatap = varp->datap();
    }
    explicit VerilatedVpioVar(const VerilatedVpioVar* varp)
        : VerilatedVpioVarBase{varp} {
        if (varp) {
            m_mask.u32 = varp->m_mask.u32;
            m_entSize = varp->m_entSize;
            m_varDatap = varp->m_varDatap;
            m_index = varp->m_index;
            // Not copying m_prevDatap, must be nullptr
        } else {
            m_mask.u32 = 0;
        }
    }
    ~VerilatedVpioVar() override {
        if (m_prevDatap) VL_DO_CLEAR(delete[] m_prevDatap, m_prevDatap = nullptr);
    }
    static VerilatedVpioVar* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVar*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t mask() const { return m_mask.u32; }
    uint8_t mask_byte(int idx) const { return m_mask.u8[idx & 3]; }
    uint32_t entSize() const { return m_entSize; }
    uint32_t index() const { return m_index; }
    uint32_t type() const override {
        return (varp()->dims() > 1) ? vpiMemory : vpiReg;  // but might be wire, logic
    }
    void* prevDatap() const { return m_prevDatap; }
    void* varDatap() const { return m_varDatap; }
    void createPrevDatap() {
        if (VL_UNLIKELY(!m_prevDatap)) {
            m_prevDatap = new uint8_t[entSize()];
            std::memcpy(prevDatap(), varp()->datap(), entSize());
        }
    }
};

class VerilatedVpioMemoryWord final : public VerilatedVpioVar {
public:
    VerilatedVpioMemoryWord(const VerilatedVar* varp, const VerilatedScope* scopep, int32_t index,
                            int offset)
        : VerilatedVpioVar{varp, scopep} {
        m_index = index;
        m_varDatap = (static_cast<uint8_t*>(varp->datap())) + entSize() * offset;
    }
    ~VerilatedVpioMemoryWord() override = default;
    static VerilatedVpioMemoryWord* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioMemoryWord*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiMemoryWord; }
    uint32_t size() const override { return varp()->packed().elements(); }
    const VerilatedRange* rangep() const override { return &(varp()->packed()); }
    const char* fullname() const override {
        static VL_THREAD_LOCAL std::string t_out;
        constexpr size_t LEN_MAX_INDEX = 25;
        char num[LEN_MAX_INDEX];
        VL_SNPRINTF(num, LEN_MAX_INDEX, "%d", m_index);
        t_out = std::string{scopep()->name()} + "." + name() + "[" + num + "]";
        return t_out.c_str();
    }
};

class VerilatedVpioVarIter final : public VerilatedVpio {
    const VerilatedScope* const m_scopep;
    VerilatedVarNameMap::const_iterator m_it;
    bool m_started = false;

public:
    explicit VerilatedVpioVarIter(const VerilatedScope* scopep)
        : m_scopep{scopep} {}
    ~VerilatedVpioVarIter() override = default;
    static VerilatedVpioVarIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVarIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiIterator; }
    vpiHandle dovpi_scan() override {
        if (VL_LIKELY(m_scopep->varsp())) {
            const VerilatedVarNameMap* const varsp = m_scopep->varsp();
            if (VL_UNLIKELY(!m_started)) {
                m_it = varsp->begin();
                m_started = true;
            } else if (VL_UNLIKELY(m_it == varsp->end())) {
                delete this;  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
                return nullptr;
            } else {
                ++m_it;
            }
            if (VL_UNLIKELY(m_it == varsp->end())) {
                delete this;  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
                return nullptr;
            }
            return ((new VerilatedVpioVar{&(m_it->second), m_scopep})->castVpiHandle());
        }
        delete this;  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        return nullptr;  // End of list - only one deep
    }
};

class VerilatedVpioMemoryWordIter final : public VerilatedVpio {
    const vpiHandle m_handle;
    const VerilatedVar* const m_varp;
    int32_t m_iteration;
    const int32_t m_direction;
    bool m_done = false;

public:
    VerilatedVpioMemoryWordIter(const vpiHandle handle, const VerilatedVar* varp)
        : m_handle{handle}
        , m_varp{varp}
        , m_iteration{varp->unpacked().right()}
        , m_direction{VL_LIKELY(varp->unpacked().left() > varp->unpacked().right()) ? 1 : -1} {}
    ~VerilatedVpioMemoryWordIter() override = default;
    static VerilatedVpioMemoryWordIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioMemoryWordIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiIterator; }
    void iterationInc() {
        if (!(m_done = (m_iteration == m_varp->unpacked().left()))) m_iteration += m_direction;
    }
    vpiHandle dovpi_scan() override {
        if (VL_UNLIKELY(m_done)) {
            delete this;  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
            return nullptr;
        }
        const vpiHandle result = vpi_handle_by_index(m_handle, m_iteration);
        iterationInc();
        return result;
    }
};

class VerilatedVpioModule final : public VerilatedVpioScope {
    const char* m_name;
    const char* m_fullname;

public:
    explicit VerilatedVpioModule(const VerilatedScope* modulep)
        : VerilatedVpioScope{modulep} {
        m_fullname = m_scopep->name();
        if (std::strncmp(m_fullname, "TOP.", 4) == 0) m_fullname += 4;
        m_name = m_scopep->identifier();
    }
    static VerilatedVpioModule* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioModule*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiModule; }
    const char* name() const override { return m_name; }
    const char* fullname() const override { return m_fullname; }
};

class VerilatedVpioModuleIter final : public VerilatedVpio {
    const std::vector<const VerilatedScope*>* m_vec;
    std::vector<const VerilatedScope*>::const_iterator m_it;

public:
    explicit VerilatedVpioModuleIter(const std::vector<const VerilatedScope*>& vec)
        : m_vec{&vec} {
        m_it = m_vec->begin();
    }
    ~VerilatedVpioModuleIter() override = default;
    static VerilatedVpioModuleIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioModuleIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    uint32_t type() const override { return vpiIterator; }
    vpiHandle dovpi_scan() override {
        if (m_it == m_vec->end()) {
            delete this;  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
            return nullptr;
        }
        const VerilatedScope* const modp = *m_it++;
        return (new VerilatedVpioModule{modp})->castVpiHandle();
    }
};

//======================================================================

using VerilatedPliCb = PLI_INT32 (*)(struct t_cb_data*);

class VerilatedVpiCbHolder final {
    // Holds information needed to call a callback
    uint64_t m_id;
    s_cb_data m_cbData;
    s_vpi_value m_value;
    VerilatedVpioVar m_varo;  // If a cbValueChange callback, the object we will return

public:
    // cppcheck-suppress uninitVar  // m_value
    VerilatedVpiCbHolder(uint64_t id, const s_cb_data* cbDatap, const VerilatedVpioVar* varop)
        : m_id{id}
        , m_cbData{*cbDatap}
        , m_varo{varop} {
        m_value.format = cbDatap->value ? cbDatap->value->format : vpiSuppressVal;
        m_cbData.value = &m_value;
        if (varop) {
            m_cbData.obj = m_varo.castVpiHandle();
            m_varo.createPrevDatap();
        } else {
            m_cbData.obj = nullptr;
        }
    }
    ~VerilatedVpiCbHolder() = default;
    VerilatedPliCb cb_rtnp() const { return m_cbData.cb_rtn; }
    s_cb_data* cb_datap() { return &m_cbData; }
    uint64_t id() const { return m_id; }
    bool invalid() const { return !m_id; }
    void invalidate() { m_id = 0; }
};

struct VerilatedVpiTimedCbsCmp {
    // Ordering sets keyed by time, then callback unique id
    bool operator()(const std::pair<QData, uint64_t>& a,
                    const std::pair<QData, uint64_t>& b) const {
        if (a.first < b.first) return true;
        if (a.first > b.first) return false;
        return a.second < b.second;
    }
};

class VerilatedVpiError;

class VerilatedVpiImp final {
    enum { CB_ENUM_MAX_VALUE = cbAtEndOfSimTime + 1 };  // Maxium callback reason
    using VpioCbList = std::list<VerilatedVpiCbHolder>;
    using VpioTimedCbs = std::map<std::pair<QData, uint64_t>, VerilatedVpiCbHolder>;

    // All only medium-speed, so use singleton function
    VpioCbList m_cbObjLists[CB_ENUM_MAX_VALUE];  // Callbacks for each supported reason
    VpioTimedCbs m_timedCbs;  // Time based callbacks
    VerilatedVpiError* m_errorInfop = nullptr;  // Container for vpi error info
    VerilatedAssertOneThread m_assertOne;  // Assert only called from single thread
    uint64_t m_nextCallbackId = 1;  // Id to identify callback

    static VerilatedVpiImp& s() {  // Singleton
        static VerilatedVpiImp s_s;
        return s_s;
    }

public:
    static void assertOneCheck() { s().m_assertOne.check(); }
    static uint64_t nextCallbackId() { return ++s().m_nextCallbackId; }

    static void cbReasonAdd(uint64_t id, const s_cb_data* cb_data_p) {
        // The passed cb_data_p was property of the user, so need to recreate
        if (VL_UNCOVERABLE(cb_data_p->reason >= CB_ENUM_MAX_VALUE)) {
            VL_FATAL_MT(__FILE__, __LINE__, "", "vpi bb reason too large");
        }
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_register_cb reason=%d id=%" PRId64 " obj=%p\n",
                                    cb_data_p->reason, id, cb_data_p->obj););
        VerilatedVpioVar* varop = nullptr;
        if (cb_data_p->reason == cbValueChange) varop = VerilatedVpioVar::castp(cb_data_p->obj);
        s().m_cbObjLists[cb_data_p->reason].emplace_back(id, cb_data_p, varop);
    }
    static void cbTimedAdd(uint64_t id, const s_cb_data* cb_data_p, QData time) {
        // The passed cb_data_p was property of the user, so need to recreate
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_register_cb reason=%d id=%" PRId64
                                    " delay=%" PRIu64 "\n",
                                    cb_data_p->reason, id, time););
        s().m_timedCbs.emplace(std::piecewise_construct,
                               std::forward_as_tuple(std::make_pair(time, id)),
                               std::forward_as_tuple(id, cb_data_p, nullptr));
    }
    static void cbReasonRemove(uint64_t id, uint32_t reason) {
        // Id might no longer exist, if already removed due to call after event, or teardown
        VpioCbList& cbObjList = s().m_cbObjLists[reason];
        // We do not remove it now as we may be iterating the list,
        // instead set to nullptr and will cleanup later
        for (auto& ir : cbObjList) {
            if (ir.id() == id) ir.invalidate();
        }
    }
    static void cbTimedRemove(uint64_t id, QData time) {
        // Id might no longer exist, if already removed due to call after event, or teardown
        const auto it = s().m_timedCbs.find(std::make_pair(time, id));
        if (VL_LIKELY(it != s().m_timedCbs.end())) it->second.invalidate();
    }
    static void callTimedCbs() VL_MT_UNSAFE_ONE {
        assertOneCheck();
        const QData time = VL_TIME_Q();
        for (auto it = s().m_timedCbs.begin(); it != s().m_timedCbs.end();) {
            if (VL_UNLIKELY(it->first.first <= time)) {
                VerilatedVpiCbHolder& ho = it->second;
                const auto last_it = it;
                ++it;
                if (VL_UNLIKELY(!ho.invalid())) {
                    VL_DEBUG_IF_PLI(
                        VL_DBG_MSGF("- vpi: timed_callback id=%" PRId64 "\n", ho.id()););
                    ho.invalidate();  // Timed callbacks are one-shot
                    (ho.cb_rtnp())(ho.cb_datap());
                }
                s().m_timedCbs.erase(last_it);
            } else {
                ++it;
            }
        }
    }
    static QData cbNextDeadline() {
        const auto it = s().m_timedCbs.cbegin();
        if (VL_LIKELY(it != s().m_timedCbs.cend())) return it->first.first;
        return ~0ULL;  // maxquad
    }
    static bool callCbs(const uint32_t reason) VL_MT_UNSAFE_ONE {
        VpioCbList& cbObjList = s().m_cbObjLists[reason];
        bool called = false;
        if (cbObjList.empty()) return called;
        const auto last = std::prev(cbObjList.end());  // prevent looping over newly added elements
        for (auto it = cbObjList.begin(); true;) {
            // cbReasonRemove sets to nullptr, so we know on removal the old end() will still exist
            const bool was_last = it == last;
            if (VL_UNLIKELY(it->invalid())) {  // Deleted earlier, cleanup
                it = cbObjList.erase(it);
                if (was_last) break;
                continue;
            }
            VerilatedVpiCbHolder& ho = *it;
            VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: reason_callback reason=%d id=%" PRId64 "\n",
                                        reason, ho.id()););
            (ho.cb_rtnp())(ho.cb_datap());
            called = true;
            if (was_last) break;
            ++it;
        }
        return called;
    }
    static bool callValueCbs() VL_MT_UNSAFE_ONE {
        assertOneCheck();
        VpioCbList& cbObjList = s().m_cbObjLists[cbValueChange];
        bool called = false;
        std::unordered_set<VerilatedVpioVar*> update;  // set of objects to update after callbacks
        if (cbObjList.empty()) return called;
        const auto last = std::prev(cbObjList.end());  // prevent looping over newly added elements
        for (auto it = cbObjList.begin(); true;) {
            // cbReasonRemove sets to nullptr, so we know on removal the old end() will still exist
            const bool was_last = it == last;
            if (VL_UNLIKELY(it->invalid())) {  // Deleted earlier, cleanup
                it = cbObjList.erase(it);
                if (was_last) break;
                continue;
            }
            VerilatedVpiCbHolder& ho = *it++;
            if (VerilatedVpioVar* const varop = VerilatedVpioVar::castp(ho.cb_datap()->obj)) {
                void* const newDatap = varop->varDatap();
                void* const prevDatap
                    = varop->prevDatap();  // Was malloced when we added the callback
                VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: value_test %s v[0]=%d/%d %p %p\n",
                                            varop->fullname(), *(static_cast<CData*>(newDatap)),
                                            *(static_cast<CData*>(prevDatap)), newDatap,
                                            prevDatap););
                if (std::memcmp(prevDatap, newDatap, varop->entSize()) != 0) {
                    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: value_callback %" PRId64 " %s v[0]=%d\n",
                                                ho.id(), varop->fullname(),
                                                *(static_cast<CData*>(newDatap))););
                    update.insert(varop);
                    vpi_get_value(ho.cb_datap()->obj, ho.cb_datap()->value);
                    (ho.cb_rtnp())(ho.cb_datap());
                    called = true;
                }
            }
            if (was_last) break;
        }
        for (const auto& ip : update) {
            std::memcpy(ip->prevDatap(), ip->varDatap(), ip->entSize());
        }
        return called;
    }

    static VerilatedVpiError* error_info() VL_MT_UNSAFE_ONE;  // getter for vpi error info
};

//======================================================================
// Statics
// Internal note: Globals may multi-construct, see verilated.cpp top.

VL_THREAD_LOCAL uint8_t* VerilatedVpio::t_freeHead = nullptr;

//======================================================================
// VerilatedVpiError
// Internal container for vpi error info

class VerilatedVpiError final {
    t_vpi_error_info m_errorInfo;
    bool m_flag = false;
    char m_buff[VL_VPI_LINE_SIZE_];
    void setError(PLI_BYTE8* message, PLI_BYTE8* code, PLI_BYTE8* file, PLI_INT32 line) {
        m_errorInfo.message = message;
        m_errorInfo.file = file;
        m_errorInfo.line = line;
        m_errorInfo.code = code;
        do_callbacks();
    }
    void do_callbacks() {
        if (getError()->level >= vpiError && Verilated::threadContextp()->fatalOnVpiError()) {
            // Stop on vpi error/unsupported
            vpi_unsupported();
        }
        // We need to run above code first because in the case that the
        // callback executes further vpi functions we will loose the error
        // as it will be overwritten.
        VerilatedVpiImp::callCbs(cbPLIError);
    }

public:
    VerilatedVpiError() {
        m_buff[0] = '\0';
        m_errorInfo.product = const_cast<PLI_BYTE8*>(Verilated::productName());
    }
    ~VerilatedVpiError() = default;
    static void selfTest() VL_MT_UNSAFE_ONE;
    VerilatedVpiError* setMessage(PLI_INT32 level) {
        m_flag = true;
        m_errorInfo.level = level;
        return this;
    }
    void setMessage(const std::string& file, PLI_INT32 line, const char* message, ...) {
        // message cannot be a const string& as va_start cannot use a reference
        static VL_THREAD_LOCAL std::string t_filehold;
        va_list args;
        va_start(args, message);
        VL_VSNPRINTF(m_buff, sizeof(m_buff), message, args);
        va_end(args);
        m_errorInfo.state = vpiPLI;
        t_filehold = file;
        setError(static_cast<PLI_BYTE8*>(m_buff), nullptr,
                 const_cast<PLI_BYTE8*>(t_filehold.c_str()), line);
    }
    p_vpi_error_info getError() {
        if (m_flag) return &m_errorInfo;
        return nullptr;
    }
    void resetError() { m_flag = false; }
    static void vpi_unsupported() {
        // Not supported yet
        const p_vpi_error_info error_info_p = VerilatedVpiImp::error_info()->getError();
        if (error_info_p) {
            VL_FATAL_MT(error_info_p->file, error_info_p->line, "", error_info_p->message);
            return;
        }
        VL_FATAL_MT(__FILE__, __LINE__, "", "vpi_unsupported called without error info set");
    }
    static const char* strFromVpiVal(PLI_INT32 vpiVal) VL_MT_SAFE;
    static const char* strFromVpiObjType(PLI_INT32 vpiVal) VL_MT_SAFE;
    static const char* strFromVpiMethod(PLI_INT32 vpiVal) VL_MT_SAFE;
    static const char* strFromVpiCallbackReason(PLI_INT32 vpiVal) VL_MT_SAFE;
    static const char* strFromVpiProp(PLI_INT32 vpiVal) VL_MT_SAFE;
};

//======================================================================
// VerilatedVpi implementation

void VerilatedVpi::callTimedCbs() VL_MT_UNSAFE_ONE { VerilatedVpiImp::callTimedCbs(); }

bool VerilatedVpi::callValueCbs() VL_MT_UNSAFE_ONE { return VerilatedVpiImp::callValueCbs(); }

bool VerilatedVpi::callCbs(uint32_t reason) VL_MT_UNSAFE_ONE {
    return VerilatedVpiImp::callCbs(reason);
}

QData VerilatedVpi::cbNextDeadline() VL_MT_UNSAFE_ONE { return VerilatedVpiImp::cbNextDeadline(); }

PLI_INT32 VerilatedVpioTimedCb::dovpi_remove_cb() {
    VerilatedVpiImp::cbTimedRemove(m_id, m_time);
    delete this;  // IEEE 37.2.2 a vpi_remove_cb does a vpi_release_handle
    return 1;
}
PLI_INT32 VerilatedVpioReasonCb::dovpi_remove_cb() {
    VerilatedVpiImp::cbReasonRemove(m_id, m_reason);
    delete this;  // IEEE 37.2.2 a vpi_remove_cb does a vpi_release_handle
    return 1;
}

//======================================================================
// VerilatedVpiImp implementation

VerilatedVpiError* VerilatedVpiImp::error_info() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::assertOneCheck();
    if (VL_UNLIKELY(!s().m_errorInfop)) s().m_errorInfop = new VerilatedVpiError;
    return s().m_errorInfop;
}

//======================================================================
// VerilatedVpiError Methods

const char* VerilatedVpiError::strFromVpiVal(PLI_INT32 vpiVal) VL_MT_SAFE {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "vpiBinStrVal",
        "vpiOctStrVal",
        "vpiDecStrVal",
        "vpiHexStrVal",
        "vpiScalarVal",
        "vpiIntVal",
        "vpiRealVal",
        "vpiStringVal",
        "vpiVectorVal",
        "vpiStrengthVal",
        "vpiTimeVal",
        "vpiObjTypeVal",
        "vpiSuppressVal",
        "vpiShortIntVal",
        "vpiLongIntVal",
        "vpiShortRealVal",
        "vpiRawTwoStateVal",
        "vpiRawFourStateVal",
    };
    // clang-format on
    if (VL_UNCOVERABLE(vpiVal < 0)) return names[0];
    return names[(vpiVal <= vpiRawFourStateVal) ? vpiVal : 0];
}
const char* VerilatedVpiError::strFromVpiObjType(PLI_INT32 vpiVal) VL_MT_SAFE {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "vpiAlways",
        "vpiAssignStmt",
        "vpiAssignment",
        "vpiBegin",
        "vpiCase",
        "vpiCaseItem",
        "vpiConstant",
        "vpiContAssign",
        "vpiDeassign",
        "vpiDefParam",
        "vpiDelayControl",
        "vpiDisable",
        "vpiEventControl",
        "vpiEventStmt",
        "vpiFor",
        "vpiForce",
        "vpiForever",
        "vpiFork",
        "vpiFuncCall",
        "vpiFunction",
        "vpiGate",
        "vpiIf",
        "vpiIfElse",
        "vpiInitial",
        "vpiIntegerVar",
        "vpiInterModPath",
        "vpiIterator",
        "vpiIODecl",
        "vpiMemory",
        "vpiMemoryWord",
        "vpiModPath",
        "vpiModule",
        "vpiNamedBegin",
        "vpiNamedEvent",
        "vpiNamedFork",
        "vpiNet",
        "vpiNetBit",
        "vpiNullStmt",
        "vpiOperation",
        "vpiParamAssign",
        "vpiParameter",
        "vpiPartSelect",
        "vpiPathTerm",
        "vpiPort",
        "vpiPortBit",
        "vpiPrimTerm",
        "vpiRealVar",
        "vpiReg",
        "vpiRegBit",
        "vpiRelease",
        "vpiRepeat",
        "vpiRepeatControl",
        "vpiSchedEvent",
        "vpiSpecParam",
        "vpiSwitch",
        "vpiSysFuncCall",
        "vpiSysTaskCall",
        "vpiTableEntry",
        "vpiTask",
        "vpiTaskCall",
        "vpiTchk",
        "vpiTchkTerm",
        "vpiTimeVar",
        "vpiTimeQueue",
        "vpiUdp",
        "vpiUdpDefn",
        "vpiUserSystf",
        "vpiVarSelect",
        "vpiWait",
        "vpiWhile",
        "vpiCondition",
        "vpiDelay",
        "vpiElseStmt",
        "vpiForIncStmt",
        "vpiForInitStmt",
        "vpiHighConn",
        "vpiLhs",
        "vpiIndex",
        "vpiLeftRange",
        "vpiLowConn",
        "vpiParent",
        "vpiRhs",
        "vpiRightRange",
        "vpiScope",
        "vpiSysTfCall",
        "vpiTchkDataTerm",
        "vpiTchkNotifier",
        "vpiTchkRefTerm",
        "vpiArgument",
        "vpiBit",
        "vpiDriver",
        "vpiInternalScope",
        "vpiLoad",
        "vpiModDataPathIn",
        "vpiModPathIn",
        "vpiModPathOut",
        "vpiOperand",
        "vpiPortInst",
        "vpiProcess",
        "vpiVariables",
        "vpiUse",
        "vpiExpr",
        "vpiPrimitive",
        "vpiStmt",
        "vpiAttribute",
        "vpiBitSelect",
        "vpiCallback",
        "vpiDelayTerm",
        "vpiDelayDevice",
        "vpiFrame",
        "vpiGateArray",
        "vpiModuleArray",
        "vpiPrimitiveArray",
        "vpiNetArray",
        "vpiRange",
        "vpiRegArray",
        "vpiSwitchArray",
        "vpiUdpArray",
        "vpiActiveTimeFormat",
        "vpiInTerm",
        "vpiInstanceArray",
        "vpiLocalDriver",
        "vpiLocalLoad",
        "vpiOutTerm",
        "vpiPorts",
        "vpiSimNet",
        "vpiTaskFunc",
        "vpiContAssignBit",
        "vpiNamedEventArray",
        "vpiIndexedPartSelect",
        "vpiBaseExpr",
        "vpiWidthExpr",
        "vpiGenScopeArray",
        "vpiGenScope",
        "vpiGenVar",
        "vpiAutomatics"
    };
    // clang-format on
    if (VL_UNCOVERABLE(vpiVal < 0)) return names[0];
    return names[(vpiVal <= vpiAutomatics) ? vpiVal : 0];
}
const char* VerilatedVpiError::strFromVpiMethod(PLI_INT32 vpiVal) VL_MT_SAFE {
    // clang-format off
    static const char* const names[] = {
        "vpiCondition",
        "vpiDelay",
        "vpiElseStmt",
        "vpiForIncStmt",
        "vpiForInitStmt",
        "vpiHighConn",
        "vpiLhs",
        "vpiIndex",
        "vpiLeftRange",
        "vpiLowConn",
        "vpiParent",
        "vpiRhs",
        "vpiRightRange",
        "vpiScope",
        "vpiSysTfCall",
        "vpiTchkDataTerm",
        "vpiTchkNotifier",
        "vpiTchkRefTerm",
        "vpiArgument",
        "vpiBit",
        "vpiDriver",
        "vpiInternalScope",
        "vpiLoad",
        "vpiModDataPathIn",
        "vpiModPathIn",
        "vpiModPathOut",
        "vpiOperand",
        "vpiPortInst",
        "vpiProcess",
        "vpiVariables",
        "vpiUse",
        "vpiExpr",
        "vpiPrimitive",
        "vpiStmt"
    };
    // clang-format on
    if (vpiVal > vpiStmt || vpiVal < vpiCondition) return "*undefined*";
    return names[vpiVal - vpiCondition];
}

const char* VerilatedVpiError::strFromVpiCallbackReason(PLI_INT32 vpiVal) VL_MT_SAFE {
    // clang-format off
    static const char* const names[] = {
        "*undefined*",
        "cbValueChange",
        "cbStmt",
        "cbForce",
        "cbRelease",
        "cbAtStartOfSimTime",
        "cbReadWriteSynch",
        "cbReadOnlySynch",
        "cbNextSimTime",
        "cbAfterDelay",
        "cbEndOfCompile",
        "cbStartOfSimulation",
        "cbEndOfSimulation",
        "cbError",
        "cbTchkViolation",
        "cbStartOfSave",
        "cbEndOfSave",
        "cbStartOfRestart",
        "cbEndOfRestart",
        "cbStartOfReset",
        "cbEndOfReset",
        "cbEnterInteractive",
        "cbExitInteractive",
        "cbInteractiveScopeChange",
        "cbUnresolvedSystf",
        "cbAssign",
        "cbDeassign",
        "cbDisable",
        "cbPLIError",
        "cbSignal",
        "cbNBASynch",
        "cbAtEndOfSimTime"
    };
    // clang-format on
    if (VL_UNCOVERABLE(vpiVal < 0)) return names[0];
    return names[(vpiVal <= cbAtEndOfSimTime) ? vpiVal : 0];
}

const char* VerilatedVpiError::strFromVpiProp(PLI_INT32 vpiVal) VL_MT_SAFE {
    // clang-format off
    static const char* const names[] = {
        "*undefined or other*",
        "vpiType",
        "vpiName",
        "vpiFullName",
        "vpiSize",
        "vpiFile",
        "vpiLineNo",
        "vpiTopModule",
        "vpiCellInstance",
        "vpiDefName",
        "vpiProtected",
        "vpiTimeUnit",
        "vpiTimePrecision",
        "vpiDefNetType",
        "vpiUnconnDrive",
        "vpiDefFile",
        "vpiDefLineNo",
        "vpiScalar",
        "vpiVector",
        "vpiExplicitName",
        "vpiDirection",
        "vpiConnByName",
        "vpiNetType",
        "vpiExplicitScalared",
        "vpiExplicitVectored",
        "vpiExpanded",
        "vpiImplicitDecl",
        "vpiChargeStrength",
        "vpiArray",
        "vpiPortIndex",
        "vpiTermIndex",
        "vpiStrength0",
        "vpiStrength1",
        "vpiPrimType",
        "vpiPolarity",
        "vpiDataPolarity",
        "vpiEdge",
        "vpiPathType",
        "vpiTchkType",
        "vpiOpType",
        "vpiConstType",
        "vpiBlocking",
        "vpiCaseType",
        "vpiFuncType",
        "vpiNetDeclAssign",
        "vpiUserDefn",
        "vpiScheduled",
        "*undefined*",
        "*undefined*",
        "vpiActive",
        "vpiAutomatic",
        "vpiCell",
        "vpiConfig",
        "vpiConstantSelect",
        "vpiDecompile",
        "vpiDefAttribute",
        "vpiDelayType",
        "vpiIteratorType",
        "vpiLibrary",
        "*undefined*",
        "vpiOffset",
        "vpiResolvedNetType",
        "vpiSaveRestartID",
        "vpiSaveRestartLocation",
        "vpiValid",
        "vpiSigned",
        "vpiStop",
        "vpiFinish",
        "vpiReset",
        "vpiSetInteractiveScope",
        "vpiLocalParam",
        "vpiModPathHasIfNone",
        "vpiIndexedPartSelectType",
        "vpiIsMemory",
        "vpiIsProtected"
    };
    // clang-format on
    if (vpiVal == vpiUndefined) return "vpiUndefined";
    return names[(vpiVal <= vpiIsProtected) ? vpiVal : 0];
}

#define SELF_CHECK_RESULT_CSTR(got, exp) \
    if (0 != std::strcmp((got), (exp))) { \
        const std::string msg \
            = std::string{"%Error: "} + "GOT = '" + (got) + "'" + "  EXP = '" + (exp) + "'"; \
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str()); \
    }

#define SELF_CHECK_ENUM_STR(fn, enumn) \
    do { \
        const char* const strVal = VerilatedVpiError::fn(enumn); \
        SELF_CHECK_RESULT_CSTR(strVal, #enumn); \
    } while (0)

void VerilatedVpi::selfTest() VL_MT_UNSAFE_ONE { VerilatedVpiError::selfTest(); }
void VerilatedVpiError::selfTest() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::assertOneCheck();

    SELF_CHECK_ENUM_STR(strFromVpiVal, vpiBinStrVal);
    SELF_CHECK_ENUM_STR(strFromVpiVal, vpiRawFourStateVal);

    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAlways);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAssignStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAssignment);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiBegin);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiCase);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiCaseItem);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiConstant);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiContAssign);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDeassign);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDefParam);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDelayControl);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDisable);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiEventControl);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiEventStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiFor);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiForce);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiForever);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiFork);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiFuncCall);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiFunction);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiGate);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIf);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIfElse);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiInitial);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIntegerVar);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiInterModPath);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIterator);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIODecl);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiMemory);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiMemoryWord);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiModPath);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiModule);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNamedBegin);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNamedEvent);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNamedFork);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNet);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNetBit);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNullStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiOperation);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiParamAssign);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiParameter);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPartSelect);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPathTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPort);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPortBit);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPrimTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRealVar);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiReg);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRegBit);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRelease);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRepeat);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRepeatControl);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSchedEvent);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSpecParam);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSwitch);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSysFuncCall);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSysTaskCall);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTableEntry);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTask);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTaskCall);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTchk);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTchkTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTimeVar);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTimeQueue);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiUdp);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiUdpDefn);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiUserSystf);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiVarSelect);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiWait);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiWhile);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiCondition);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDelay);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiElseStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiForIncStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiForInitStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiHighConn);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiLhs);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIndex);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiLeftRange);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiLowConn);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiParent);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRhs);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRightRange);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiScope);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSysTfCall);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTchkDataTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTchkNotifier);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTchkRefTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiArgument);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiBit);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDriver);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiInternalScope);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiLoad);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiModDataPathIn);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiModPathIn);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiModPathOut);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiOperand);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPortInst);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiProcess);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiVariables);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiUse);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiExpr);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPrimitive);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiStmt);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAttribute);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiBitSelect);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiCallback);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDelayTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiDelayDevice);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiFrame);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiGateArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiModuleArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPrimitiveArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNetArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRange);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiRegArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSwitchArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiUdpArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiActiveTimeFormat);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiInTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiInstanceArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiLocalDriver);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiLocalLoad);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiOutTerm);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiPorts);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiSimNet);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiTaskFunc);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiContAssignBit);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiNamedEventArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiIndexedPartSelect);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiBaseExpr);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiWidthExpr);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiGenScopeArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiGenScope);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiGenVar);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAutomatics);

    SELF_CHECK_ENUM_STR(strFromVpiMethod, vpiCondition);
    SELF_CHECK_ENUM_STR(strFromVpiMethod, vpiStmt);

    SELF_CHECK_ENUM_STR(strFromVpiCallbackReason, cbValueChange);
    SELF_CHECK_ENUM_STR(strFromVpiCallbackReason, cbAtEndOfSimTime);

    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiType);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiProtected);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiDirection);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiTermIndex);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiConstType);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiAutomatic);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiOffset);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiStop);
    SELF_CHECK_ENUM_STR(strFromVpiProp, vpiIsProtected);
}

#undef SELF_CHECK_ENUM_STR
#undef SELF_CHECK_RESULT_CSTR

//======================================================================
// callback related

vpiHandle vpi_register_cb(p_cb_data cb_data_p) {
    // Returns handle so user can remove the callback, user must vpi_release_handle it
    // Don't confuse with the callback-activated t_cb_data object handle
    // which is the object causing the callback rather than the callback itself
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!cb_data_p)) {
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s : callback data pointer is null", __func__);
        return nullptr;
    }
    switch (cb_data_p->reason) {
    case cbAfterDelay: {
        QData time = 0;
        if (cb_data_p->time) time = VL_SET_QII(cb_data_p->time->high, cb_data_p->time->low);
        const QData abstime = VL_TIME_Q() + time;
        const uint64_t id = VerilatedVpiImp::nextCallbackId();
        VerilatedVpioTimedCb* const vop = new VerilatedVpioTimedCb{id, abstime};
        VerilatedVpiImp::cbTimedAdd(id, cb_data_p, abstime);
        return vop->castVpiHandle();
    }
    case cbReadWriteSynch:  // FALLTHRU // Supported via vlt_main.cpp
    case cbReadOnlySynch:  // FALLTHRU // Supported via vlt_main.cpp
    case cbNextSimTime:  // FALLTHRU // Supported via vlt_main.cpp
    case cbStartOfSimulation:  // FALLTHRU // Supported via vlt_main.cpp
    case cbEndOfSimulation:  // FALLTHRU // Supported via vlt_main.cpp
    case cbValueChange:  // FALLTHRU // Supported via vlt_main.cpp
    case cbPLIError:  // FALLTHRU // NOP, but need to return handle, so make object
    case cbEnterInteractive:  // FALLTHRU // NOP, but need to return handle, so make object
    case cbExitInteractive:  // FALLTHRU // NOP, but need to return handle, so make object
    case cbInteractiveScopeChange: {  // FALLTHRU // NOP, but need to return handle, so make object
        const uint64_t id = VerilatedVpiImp::nextCallbackId();
        VerilatedVpioReasonCb* const vop = new VerilatedVpioReasonCb{id, cb_data_p->reason};
        VerilatedVpiImp::cbReasonAdd(id, cb_data_p);
        return vop->castVpiHandle();
    }
    default:
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Unsupported callback type %s", __func__,
                        VerilatedVpiError::strFromVpiCallbackReason(cb_data_p->reason));
        return nullptr;
    }
}

PLI_INT32 vpi_remove_cb(vpiHandle cb_obj) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_remove_cb %p\n", cb_obj););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    VerilatedVpio* const vop = VerilatedVpio::castp(cb_obj);
    if (VL_UNLIKELY(!vop)) return 0;
    return vop->dovpi_remove_cb();
}

void vpi_get_cb_info(vpiHandle /*object*/, p_cb_data /*cb_data_p*/) { VL_VPI_UNIMP_(); }
vpiHandle vpi_register_systf(p_vpi_systf_data /*systf_data_p*/) {
    VL_VPI_UNIMP_();
    return nullptr;
}
void vpi_get_systf_info(vpiHandle /*object*/, p_vpi_systf_data /*systf_data_p*/) {
    VL_VPI_UNIMP_();
}

// for obtaining handles

vpiHandle vpi_handle_by_name(PLI_BYTE8* namep, vpiHandle scope) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    if (VL_UNLIKELY(!namep)) return nullptr;
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle_by_name %s %p\n", namep, scope););
    const VerilatedVar* varp = nullptr;
    const VerilatedScope* scopep;
    const VerilatedVpioScope* const voScopep = VerilatedVpioScope::castp(scope);
    std::string scopeAndName = namep;
    if (voScopep) {
        scopeAndName = std::string{voScopep->fullname()} + "." + namep;
        namep = const_cast<PLI_BYTE8*>(scopeAndName.c_str());
    }
    {
        // This doesn't yet follow the hierarchy in the proper way
        scopep = Verilated::threadContextp()->scopeFind(namep);
        if (scopep) {  // Whole thing found as a scope
            if (scopep->type() == VerilatedScope::SCOPE_MODULE) {
                return (new VerilatedVpioModule{scopep})->castVpiHandle();
            } else {
                return (new VerilatedVpioScope{scopep})->castVpiHandle();
            }
        }
        const char* baseNamep = scopeAndName.c_str();
        std::string scopename;
        const char* const dotp = std::strrchr(namep, '.');
        if (VL_LIKELY(dotp)) {
            baseNamep = dotp + 1;
            const size_t len = dotp - namep;
            scopename = std::string{namep, len};
        }

        if (scopename.find('.') == std::string::npos) {
            // This is a toplevel, hence search in our TOP ports first.
            scopep = Verilated::threadContextp()->scopeFind("TOP");
            if (scopep) varp = scopep->varFind(baseNamep);
        }
        if (!varp) {
            scopep = Verilated::threadContextp()->scopeFind(scopename.c_str());
            if (!scopep) return nullptr;
            varp = scopep->varFind(baseNamep);
        }
    }
    if (!varp) return nullptr;

    if (varp->isParam()) {
        return (new VerilatedVpioParam{varp, scopep})->castVpiHandle();
    } else {
        return (new VerilatedVpioVar{varp, scopep})->castVpiHandle();
    }
}

vpiHandle vpi_handle_by_index(vpiHandle object, PLI_INT32 indx) {
    // Used to get array entries
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle_by_index %p %d\n", object, indx););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    // Memory words are not indexable
    const VerilatedVpioMemoryWord* const vop = VerilatedVpioMemoryWord::castp(object);
    if (VL_UNLIKELY(vop)) return nullptr;
    const VerilatedVpioVar* const varop = VerilatedVpioVar::castp(object);
    if (VL_LIKELY(varop)) {
        if (varop->varp()->dims() < 2) return nullptr;
        if (VL_LIKELY(varop->varp()->unpacked().left() >= varop->varp()->unpacked().right())) {
            if (VL_UNLIKELY(indx > varop->varp()->unpacked().left()
                            || indx < varop->varp()->unpacked().right()))
                return nullptr;
            return (new VerilatedVpioMemoryWord{varop->varp(), varop->scopep(), indx,
                                                indx - varop->varp()->unpacked().right()})
                ->castVpiHandle();
        }
        if (VL_UNLIKELY(indx < varop->varp()->unpacked().left()
                        || indx > varop->varp()->unpacked().right()))
            return nullptr;
        return (new VerilatedVpioMemoryWord{varop->varp(), varop->scopep(), indx,
                                            indx - varop->varp()->unpacked().left()})
            ->castVpiHandle();
    }
    VL_VPI_INTERNAL_(__FILE__, __LINE__, "%s : can't resolve handle", __func__);
    return nullptr;
}

// for traversing relationships

vpiHandle vpi_handle(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle %d %p\n", type, object););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    switch (type) {
    case vpiLeftRange: {
        if (const VerilatedVpioVarBase* const vop = VerilatedVpioVarBase::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return nullptr;
            return (new VerilatedVpioConst{vop->rangep()->left()})->castVpiHandle();
        } else if (const VerilatedVpioRange* const vop = VerilatedVpioRange::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return nullptr;
            return (new VerilatedVpioConst{vop->rangep()->left()})->castVpiHandle();
        }
        VL_VPI_WARNING_(__FILE__, __LINE__,
                        "%s: Unsupported vpiHandle (%p) for type %s, nothing will be returned",
                        __func__, object, VerilatedVpiError::strFromVpiMethod(type));
        return nullptr;
    }
    case vpiRightRange: {
        if (const VerilatedVpioVarBase* const vop = VerilatedVpioVarBase::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return nullptr;
            return (new VerilatedVpioConst{vop->rangep()->right()})->castVpiHandle();
        } else if (const VerilatedVpioRange* const vop = VerilatedVpioRange::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return nullptr;
            return (new VerilatedVpioConst{vop->rangep()->right()})->castVpiHandle();
        }
        VL_VPI_WARNING_(__FILE__, __LINE__,
                        "%s: Unsupported vpiHandle (%p) for type %s, nothing will be returned",
                        __func__, object, VerilatedVpiError::strFromVpiMethod(type));
        return nullptr;
    }
    case vpiIndex: {
        const VerilatedVpioVar* const vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return nullptr;
        const int32_t val = vop->index();
        return (new VerilatedVpioConst{val})->castVpiHandle();
    }
    case vpiScope: {
        const VerilatedVpioVarBase* const vop = VerilatedVpioVarBase::castp(object);
        if (VL_UNLIKELY(!vop)) return nullptr;
        return (new VerilatedVpioScope{vop->scopep()})->castVpiHandle();
    }
    case vpiParent: {
        const VerilatedVpioMemoryWord* const vop = VerilatedVpioMemoryWord::castp(object);
        if (VL_UNLIKELY(!vop)) return nullptr;
        return (new VerilatedVpioVar{vop->varp(), vop->scopep()})->castVpiHandle();
    }
    default:
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        __func__, VerilatedVpiError::strFromVpiMethod(type));
        return nullptr;
    }
}

vpiHandle vpi_handle_multi(PLI_INT32 /*type*/, vpiHandle /*refHandle1*/, vpiHandle /*refHandle2*/,
                           ...) {
    VL_VPI_UNIMP_();
    return nullptr;
}

vpiHandle vpi_iterate(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_iterate %d %p\n", type, object););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    switch (type) {
    case vpiMemoryWord: {
        const VerilatedVpioVar* const vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return nullptr;
        if (vop->varp()->dims() < 2) return nullptr;
        if (vop->varp()->dims() > 2) {
            VL_VPI_WARNING_(__FILE__, __LINE__,
                            "%s: %s, object %s has unsupported number of indices (%d)", __func__,
                            VerilatedVpiError::strFromVpiMethod(type), vop->fullname(),
                            vop->varp()->dims());
        }
        return (new VerilatedVpioMemoryWordIter{object, vop->varp()})->castVpiHandle();
    }
    case vpiRange: {
        const VerilatedVpioVar* const vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return nullptr;
        if (vop->varp()->dims() < 2) return nullptr;
        // Unsupported is multidim list
        if (vop->varp()->dims() > 2) {
            VL_VPI_WARNING_(__FILE__, __LINE__,
                            "%s: %s, object %s has unsupported number of indices (%d)", __func__,
                            VerilatedVpiError::strFromVpiMethod(type), vop->fullname(),
                            vop->varp()->dims());
        }
        return ((new VerilatedVpioRangeIter{vop->rangep()})->castVpiHandle());
    }
    case vpiReg: {
        const VerilatedVpioScope* const vop = VerilatedVpioScope::castp(object);
        if (VL_UNLIKELY(!vop)) return nullptr;
        return ((new VerilatedVpioVarIter{vop->scopep()})->castVpiHandle());
    }
    case vpiModule: {
        const VerilatedVpioModule* const vop = VerilatedVpioModule::castp(object);
        const VerilatedHierarchyMap* const map = VerilatedImp::hierarchyMap();
        const VerilatedScope* const modp = vop ? vop->scopep() : nullptr;
        const auto it = vlstd::as_const(map)->find(const_cast<VerilatedScope*>(modp));
        if (it == map->end()) return nullptr;
        return ((new VerilatedVpioModuleIter{it->second})->castVpiHandle());
    }
    default:
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        __func__, VerilatedVpiError::strFromVpiObjType(type));
        return nullptr;
    }
}
vpiHandle vpi_scan(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_scan %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    VerilatedVpio* const vop = VerilatedVpio::castp(object);
    if (VL_UNLIKELY(!vop)) return nullptr;
    return vop->dovpi_scan();
}

// for processing properties

PLI_INT32 vpi_get(PLI_INT32 property, vpiHandle object) {
    // Leave this in the header file - in many cases the compiler can constant propagate "object"
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get %d %p\n", property, object););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    switch (property) {
    case vpiTimePrecision: {
        return Verilated::threadContextp()->timeprecision();
    }
    case vpiTimeUnit: {
        const VerilatedVpioScope* const vop = VerilatedVpioScope::castp(object);
        if (!vop)
            return Verilated::threadContextp()->timeunit();  // Null asks for global, not unlikely
        return vop->scopep()->timeunit();
    }
    case vpiType: {
        const VerilatedVpio* const vop = VerilatedVpio::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return vop->type();
    }
    case vpiDirection: {
        // By forthought, the directions already are vpi enumerated
        const VerilatedVpioVarBase* const vop = VerilatedVpioVarBase::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return vop->varp()->vldir();
    }
    case vpiScalar:  // FALLTHRU
    case vpiVector: {
        const VerilatedVpioVarBase* const vop = VerilatedVpioVarBase::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return (property == vpiVector) ^ (vop->varp()->dims() == 0);
    }
    case vpiSize: {
        const VerilatedVpioVarBase* const vop = VerilatedVpioVarBase::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return vop->size();
    }
    default:
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        __func__, VerilatedVpiError::strFromVpiProp(property));
        return 0;
    }
}

PLI_INT64 vpi_get64(PLI_INT32 /*property*/, vpiHandle /*object*/) {
    VL_VPI_UNIMP_();
    return 0;
}

PLI_BYTE8* vpi_get_str(PLI_INT32 property, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get_str %d %p\n", property, object););
    VerilatedVpiImp::assertOneCheck();
    const VerilatedVpio* const vop = VerilatedVpio::castp(object);
    VL_VPI_ERROR_RESET_();
    if (VL_UNLIKELY(!vop)) return nullptr;
    switch (property) {
    case vpiName: {
        return const_cast<PLI_BYTE8*>(vop->name());
    }
    case vpiFullName: {
        return const_cast<PLI_BYTE8*>(vop->fullname());
    }
    case vpiDefName: {
        return const_cast<PLI_BYTE8*>(vop->defname());
    }
    case vpiType: {
        return const_cast<PLI_BYTE8*>(VerilatedVpiError::strFromVpiObjType(vop->type()));
    }
    default:
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        __func__, VerilatedVpiError::strFromVpiProp(property));
        return nullptr;
    }
}

// delay processing

void vpi_get_delays(vpiHandle /*object*/, p_vpi_delay /*delay_p*/) { VL_VPI_UNIMP_(); }
void vpi_put_delays(vpiHandle /*object*/, p_vpi_delay /*delay_p*/) { VL_VPI_UNIMP_(); }

// value processing
bool vl_check_format(const VerilatedVar* varp, const p_vpi_value valuep, const char* fullname,
                     bool isGetValue) {
    bool status = true;
    if ((valuep->format == vpiVectorVal) || (valuep->format == vpiBinStrVal)
        || (valuep->format == vpiOctStrVal) || (valuep->format == vpiHexStrVal)) {
        switch (varp->vltype()) {
        case VLVT_UINT8:
        case VLVT_UINT16:
        case VLVT_UINT32:
        case VLVT_UINT64:
        case VLVT_WDATA: return status;
        default: status = false;
        }
    } else if (valuep->format == vpiDecStrVal) {
        switch (varp->vltype()) {
        case VLVT_UINT8:
        case VLVT_UINT16:
        case VLVT_UINT32:
        case VLVT_UINT64: return status;
        default: status = false;
        }
    } else if (valuep->format == vpiStringVal) {
        switch (varp->vltype()) {
        case VLVT_UINT8:
        case VLVT_UINT16:
        case VLVT_UINT32:
        case VLVT_UINT64:
        case VLVT_WDATA: return status;
        case VLVT_STRING:
            if (isGetValue) {
                return status;
            } else {
                status = false;
                break;
            }
        default: status = false;
        }
    } else if (valuep->format == vpiIntVal) {
        switch (varp->vltype()) {
        case VLVT_UINT8:
        case VLVT_UINT16:
        case VLVT_UINT32: return status;
        default: status = false;
        }
    } else if (valuep->format == vpiSuppressVal) {
        return status;
    } else {
        status = false;
    }
    VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s", __func__,
                  VerilatedVpiError::strFromVpiVal(valuep->format), fullname);
    return status;
}

void vl_get_value(const VerilatedVar* varp, void* varDatap, p_vpi_value valuep,
                  const char* fullname) {
    if (!vl_check_format(varp, valuep, fullname, true)) return;
    // Maximum required size is for binary string, one byte per bit plus null termination
    static VL_THREAD_LOCAL char t_outStr[VL_VALUE_STRING_MAX_WORDS * VL_EDATASIZE + 1];
    // cppcheck-suppress variableScope
    static const VL_THREAD_LOCAL int t_outStrSz = sizeof(t_outStr) - 1;
    // We used to presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
    // This may cause backward compatibility issues with older code.
    if (valuep->format == vpiVectorVal) {
        // Vector pointer must come from our memory pool
        // It only needs to persist until the next vpi_get_value
        static VL_THREAD_LOCAL t_vpi_vecval t_out[VL_VALUE_STRING_MAX_WORDS * 2];
        valuep->value.vector = t_out;
        if (varp->vltype() == VLVT_UINT8) {
            t_out[0].aval = *(reinterpret_cast<CData*>(varDatap));
            t_out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_UINT16) {
            t_out[0].aval = *(reinterpret_cast<SData*>(varDatap));
            t_out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_UINT32) {
            t_out[0].aval = *(reinterpret_cast<IData*>(varDatap));
            t_out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_UINT64) {
            const QData data = *(reinterpret_cast<QData*>(varDatap));
            t_out[1].aval = static_cast<IData>(data >> 32ULL);
            t_out[1].bval = 0;
            t_out[0].aval = static_cast<IData>(data);
            t_out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_WDATA) {
            const int words = VL_WORDS_I(varp->packed().elements());
            if (VL_UNCOVERABLE(words >= VL_VALUE_STRING_MAX_WORDS)) {
                VL_FATAL_MT(__FILE__, __LINE__, "",
                            "vpi_get_value with more than VL_VALUE_STRING_MAX_WORDS; increase and "
                            "recompile");
            }
            const WDataInP datap = (reinterpret_cast<EData*>(varDatap));
            for (int i = 0; i < words; ++i) {
                t_out[i].aval = datap[i];
                t_out[i].bval = 0;
            }
            return;
        }
    } else if (valuep->format == vpiBinStrVal) {
        valuep->value.str = t_outStr;
        int bits = varp->packed().elements();
        const CData* datap = (reinterpret_cast<CData*>(varDatap));
        int i;
        if (bits > t_outStrSz) {
            // limit maximum size of output to size of buffer to prevent overrun.
            bits = t_outStrSz;
            VL_VPI_WARNING_(
                __FILE__, __LINE__,
                "%s: Truncating string value of %s for %s"
                " as buffer size (%d, VL_VALUE_STRING_MAX_WORDS=%d) is less than required (%d)",
                __func__, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, t_outStrSz,
                VL_VALUE_STRING_MAX_WORDS, bits);
        }
        for (i = 0; i < bits; ++i) {
            const char val = (datap[i >> 3] >> (i & 7)) & 1;
            t_outStr[bits - i - 1] = val ? '1' : '0';
        }
        t_outStr[i] = '\0';
        return;
    } else if (valuep->format == vpiOctStrVal) {
        valuep->value.str = t_outStr;
        int chars = (varp->packed().elements() + 2) / 3;
        const int bytes = VL_BYTES_I(varp->packed().elements());
        const CData* datap = (reinterpret_cast<CData*>(varDatap));
        int i;
        if (chars > t_outStrSz) {
            // limit maximum size of output to size of buffer to prevent overrun.
            VL_VPI_WARNING_(
                __FILE__, __LINE__,
                "%s: Truncating string value of %s for %s"
                " as buffer size (%d, VL_VALUE_STRING_MAX_WORDS=%d) is less than required (%d)",
                __func__, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, t_outStrSz,
                VL_VALUE_STRING_MAX_WORDS, chars);
            chars = t_outStrSz;
        }
        for (i = 0; i < chars; ++i) {
            const div_t idx = div(i * 3, 8);
            int val = datap[idx.quot];
            if ((idx.quot + 1) < bytes) {
                // if the next byte is valid or that in
                // for when the required 3 bits straddle adjacent bytes
                val |= datap[idx.quot + 1] << 8;
            }
            // align so least significant 3 bits represent octal char
            val >>= idx.rem;
            if (i == (chars - 1)) {
                // most signifcant char, mask off non existant bits when vector
                // size is not a multiple of 3
                const unsigned int rem = varp->packed().elements() % 3;
                if (rem) {
                    // generate bit mask & zero non existant bits
                    val &= (1 << rem) - 1;
                }
            }
            t_outStr[chars - i - 1] = '0' + (val & 7);
        }
        t_outStr[i] = '\0';
        return;
    } else if (valuep->format == vpiDecStrVal) {
        valuep->value.str = t_outStr;
        // outStrSz does not include nullptr termination so add one
        if (varp->vltype() == VLVT_UINT8) {
            VL_SNPRINTF(t_outStr, t_outStrSz + 1, "%hhu",
                        static_cast<unsigned char>(*(reinterpret_cast<CData*>(varDatap))));
            return;
        } else if (varp->vltype() == VLVT_UINT16) {
            VL_SNPRINTF(t_outStr, t_outStrSz + 1, "%hu",
                        static_cast<unsigned short>(*(reinterpret_cast<SData*>(varDatap))));
            return;
        } else if (varp->vltype() == VLVT_UINT32) {
            VL_SNPRINTF(t_outStr, t_outStrSz + 1, "%u",
                        static_cast<unsigned int>(*(reinterpret_cast<IData*>(varDatap))));
            return;
        } else if (varp->vltype() == VLVT_UINT64) {
            VL_SNPRINTF(t_outStr, t_outStrSz + 1, "%llu",
                        static_cast<unsigned long long>(*(reinterpret_cast<QData*>(varDatap))));
            return;
        }
    } else if (valuep->format == vpiHexStrVal) {
        valuep->value.str = t_outStr;
        int chars = (varp->packed().elements() + 3) >> 2;
        const CData* datap = (reinterpret_cast<CData*>(varDatap));
        int i;
        if (chars > t_outStrSz) {
            // limit maximum size of output to size of buffer to prevent overrun.
            VL_VPI_WARNING_(
                __FILE__, __LINE__,
                "%s: Truncating string value of %s for %s"
                " as buffer size (%d, VL_VALUE_STRING_MAX_WORDS=%d) is less than required (%d)",
                __func__, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, t_outStrSz,
                VL_VALUE_STRING_MAX_WORDS, chars);
            chars = t_outStrSz;
        }
        for (i = 0; i < chars; ++i) {
            char val = (datap[i >> 1] >> ((i & 1) << 2)) & 15;
            if (i == (chars - 1)) {
                // most signifcant char, mask off non existant bits when vector
                // size is not a multiple of 4
                const unsigned int rem = varp->packed().elements() & 3;
                if (rem) {
                    // generate bit mask & zero non existant bits
                    val &= (1 << rem) - 1;
                }
            }
            t_outStr[chars - i - 1] = "0123456789abcdef"[static_cast<int>(val)];
        }
        t_outStr[i] = '\0';
        return;
    } else if (valuep->format == vpiStringVal) {
        if (varp->vltype() == VLVT_STRING) {
            valuep->value.str = reinterpret_cast<char*>(varDatap);
            return;
        } else {
            valuep->value.str = t_outStr;
            int bytes = VL_BYTES_I(varp->packed().elements());
            const CData* datap = (reinterpret_cast<CData*>(varDatap));
            int i;
            if (bytes > t_outStrSz) {
                // limit maximum size of output to size of buffer to prevent overrun.
                VL_VPI_WARNING_(__FILE__, __LINE__,
                                "%s: Truncating string value of %s for %s"
                                " as buffer size (%d, VL_VALUE_STRING_MAX_WORDS=%d) is less than "
                                "required (%d)",
                                __func__, VerilatedVpiError::strFromVpiVal(valuep->format),
                                fullname, t_outStrSz, VL_VALUE_STRING_MAX_WORDS, bytes);
                bytes = t_outStrSz;
            }
            for (i = 0; i < bytes; ++i) {
                const char val = datap[bytes - i - 1];
                // other simulators replace [leading?] zero chars with spaces, replicate here.
                t_outStr[i] = val ? val : ' ';
            }
            t_outStr[i] = '\0';
            return;
        }
    } else if (valuep->format == vpiIntVal) {
        if (varp->vltype() == VLVT_UINT8) {
            valuep->value.integer = *(reinterpret_cast<CData*>(varDatap));
            return;
        } else if (varp->vltype() == VLVT_UINT16) {
            valuep->value.integer = *(reinterpret_cast<SData*>(varDatap));
            return;
        } else if (varp->vltype() == VLVT_UINT32) {
            valuep->value.integer = *(reinterpret_cast<IData*>(varDatap));
            return;
        }
    } else if (valuep->format == vpiSuppressVal) {
        return;
    }
    VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s", __func__,
                  VerilatedVpiError::strFromVpiVal(valuep->format), fullname);
}

void vpi_get_value(vpiHandle object, p_vpi_value valuep) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get_value %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    if (VL_UNLIKELY(!valuep)) return;

    if (const VerilatedVpioVar* const vop = VerilatedVpioVar::castp(object)) {
        vl_get_value(vop->varp(), vop->varDatap(), valuep, vop->fullname());
        return;
    } else if (const VerilatedVpioParam* const vop = VerilatedVpioParam::castp(object)) {
        vl_get_value(vop->varp(), vop->varDatap(), valuep, vop->fullname());
        return;
    } else if (const VerilatedVpioConst* const vop = VerilatedVpioConst::castp(object)) {
        if (valuep->format == vpiIntVal) {
            valuep->value.integer = vop->num();
            return;
        }
        VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s", __func__,
                      VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
        return;
    }
    VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported vpiHandle (%p)", __func__, object);
}

vpiHandle vpi_put_value(vpiHandle object, p_vpi_value valuep, p_vpi_time /*time_p*/,
                        PLI_INT32 /*flags*/) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_put_value %p %p\n", object, valuep););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    if (VL_UNLIKELY(!valuep)) {
        VL_VPI_WARNING_(__FILE__, __LINE__, "Ignoring vpi_put_value with nullptr value pointer");
        return nullptr;
    }
    if (const VerilatedVpioVar* const vop = VerilatedVpioVar::castp(object)) {
        VL_DEBUG_IF_PLI(
            VL_DBG_MSGF("- vpi:   vpi_put_value name=%s fmt=%d vali=%d\n", vop->fullname(),
                        valuep->format, valuep->value.integer);
            VL_DBG_MSGF("- vpi:   varp=%p  putatp=%p\n", vop->varp()->datap(), vop->varDatap()););

        if (VL_UNLIKELY(!vop->varp()->isPublicRW())) {
            VL_VPI_WARNING_(__FILE__, __LINE__,
                            "Ignoring vpi_put_value to signal marked read-only,"
                            " use public_flat_rw instead: %s",
                            vop->fullname());
            return nullptr;
        }
        if (!vl_check_format(vop->varp(), valuep, vop->fullname(), false)) return nullptr;
        if (valuep->format == vpiVectorVal) {
            if (VL_UNLIKELY(!valuep->value.vector)) return nullptr;
            if (vop->varp()->vltype() == VLVT_UINT8) {
                *(reinterpret_cast<CData*>(vop->varDatap()))
                    = valuep->value.vector[0].aval & vop->mask();
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT16) {
                *(reinterpret_cast<SData*>(vop->varDatap()))
                    = valuep->value.vector[0].aval & vop->mask();
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT32) {
                *(reinterpret_cast<IData*>(vop->varDatap()))
                    = valuep->value.vector[0].aval & vop->mask();
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT64) {
                *(reinterpret_cast<QData*>(vop->varDatap())) = VL_SET_QII(
                    valuep->value.vector[1].aval & vop->mask(), valuep->value.vector[0].aval);
                return object;
            } else if (vop->varp()->vltype() == VLVT_WDATA) {
                const int words = VL_WORDS_I(vop->varp()->packed().elements());
                WDataOutP datap = (reinterpret_cast<EData*>(vop->varDatap()));
                for (int i = 0; i < words; ++i) {
                    datap[i] = valuep->value.vector[i].aval;
                    if (i == (words - 1)) datap[i] &= vop->mask();
                }
                return object;
            }
        } else if (valuep->format == vpiBinStrVal) {
            const int bits = vop->varp()->packed().elements();
            const int len = std::strlen(valuep->value.str);
            CData* const datap = (reinterpret_cast<CData*>(vop->varDatap()));
            for (int i = 0; i < bits; ++i) {
                const char set = (i < len) ? (valuep->value.str[len - i - 1] == '1') : 0;
                // zero bits 7:1 of byte when assigning to bit 0, else
                // or in 1 if bit set
                if (i & 7) {
                    datap[i >> 3] |= set << (i & 7);
                } else {
                    datap[i >> 3] = set;
                }
            }
            return object;
        } else if (valuep->format == vpiOctStrVal) {
            const int chars = (vop->varp()->packed().elements() + 2) / 3;
            const int bytes = VL_BYTES_I(vop->varp()->packed().elements());
            const int len = std::strlen(valuep->value.str);
            CData* const datap = (reinterpret_cast<CData*>(vop->varDatap()));
            div_t idx;
            datap[0] = 0;  // reset zero'th byte
            for (int i = 0; i < chars; ++i) {
                union {
                    char byte[2];
                    uint16_t half;
                } val;
                idx = div(i * 3, 8);
                if (i < len) {
                    // ignore illegal chars
                    const char digit = valuep->value.str[len - i - 1];
                    if (digit >= '0' && digit <= '7') {
                        val.half = digit - '0';
                    } else {
                        VL_VPI_WARNING_(__FILE__, __LINE__,
                                        "%s: Non octal character '%c' in '%s' as value %s for %s",
                                        __func__, digit, valuep->value.str,
                                        VerilatedVpiError::strFromVpiVal(valuep->format),
                                        vop->fullname());
                        val.half = 0;
                    }
                } else {
                    val.half = 0;
                }
                // align octal character to position within vector, note that
                // the three bits may straddle a byte boundary so two byte wide
                // assignments are made to adjacent bytes - but not if the least
                // significant byte of the aligned value is the most significant
                // byte of the destination.
                val.half <<= idx.rem;
                datap[idx.quot] |= val.byte[0];  // or in value
                if ((idx.quot + 1) < bytes) {
                    datap[idx.quot + 1] = val.byte[1];  // this also resets
                    // all bits to 0 prior to or'ing above
                }
            }
            // mask off non-existent bits in the most significant byte
            if (idx.quot == (bytes - 1)) {
                datap[idx.quot] &= vop->mask_byte(idx.quot);
            } else if (idx.quot + 1 == (bytes - 1)) {
                datap[idx.quot + 1] &= vop->mask_byte(idx.quot + 1);
            }
            // zero off remaining top bytes
            for (int i = idx.quot + 2; i < bytes; ++i) datap[i] = 0;
            return object;
        } else if (valuep->format == vpiDecStrVal) {
            char remainder[16];
            unsigned long long val;
            const int success = std::sscanf(valuep->value.str, "%30llu%15s", &val, remainder);
            if (success < 1) {
                VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Parsing failed for '%s' as value %s for %s",
                              __func__, valuep->value.str,
                              VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
                return nullptr;
            }
            if (success > 1) {
                VL_VPI_WARNING_(__FILE__, __LINE__,
                                "%s: Trailing garbage '%s' in '%s' as value %s for %s", __func__,
                                remainder, valuep->value.str,
                                VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
            }
            if (vop->varp()->vltype() == VLVT_UINT8) {
                *(reinterpret_cast<CData*>(vop->varDatap())) = val & vop->mask();
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT16) {
                *(reinterpret_cast<SData*>(vop->varDatap())) = val & vop->mask();
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT32) {
                *(reinterpret_cast<IData*>(vop->varDatap())) = val & vop->mask();
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT64) {
                *(reinterpret_cast<QData*>(vop->varDatap())) = val;
                (reinterpret_cast<IData*>(vop->varDatap()))[1] &= vop->mask();
                return object;
            }
        } else if (valuep->format == vpiHexStrVal) {
            const int chars = (vop->varp()->packed().elements() + 3) >> 2;
            CData* const datap = (reinterpret_cast<CData*>(vop->varDatap()));
            const char* val = valuep->value.str;
            // skip hex ident if one is detected at the start of the string
            if (val[0] == '0' && (val[1] == 'x' || val[1] == 'X')) val += 2;
            const int len = std::strlen(val);
            for (int i = 0; i < chars; ++i) {
                char hex;
                // compute hex digit value
                if (i < len) {
                    const char digit = val[len - i - 1];
                    if (digit >= '0' && digit <= '9') {
                        hex = digit - '0';
                    } else if (digit >= 'a' && digit <= 'f') {
                        hex = digit - 'a' + 10;
                    } else if (digit >= 'A' && digit <= 'F') {
                        hex = digit - 'A' + 10;
                    } else {
                        VL_VPI_WARNING_(__FILE__, __LINE__,
                                        "%s: Non hex character '%c' in '%s' as value %s for %s",
                                        __func__, digit, valuep->value.str,
                                        VerilatedVpiError::strFromVpiVal(valuep->format),
                                        vop->fullname());
                        hex = 0;
                    }
                } else {
                    hex = 0;
                }
                // assign hex digit value to destination
                if (i & 1) {
                    datap[i >> 1] |= hex << 4;
                } else {
                    datap[i >> 1] = hex;  // this also resets all
                    // bits to 0 prior to or'ing above of the msb
                }
            }
            // apply bit mask to most significant byte
            datap[(chars - 1) >> 1] &= vop->mask_byte((chars - 1) >> 1);
            return object;
        } else if (valuep->format == vpiStringVal) {
            const int bytes = VL_BYTES_I(vop->varp()->packed().elements());
            const int len = std::strlen(valuep->value.str);
            CData* const datap = (reinterpret_cast<CData*>(vop->varDatap()));
            for (int i = 0; i < bytes; ++i) {
                // prepend with 0 values before placing string the least significant bytes
                datap[i] = (i < len) ? valuep->value.str[len - i - 1] : 0;
            }
            return object;
        } else if (valuep->format == vpiIntVal) {
            if (vop->varp()->vltype() == VLVT_UINT8) {
                *(reinterpret_cast<CData*>(vop->varDatap())) = vop->mask() & valuep->value.integer;
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT16) {
                *(reinterpret_cast<SData*>(vop->varDatap())) = vop->mask() & valuep->value.integer;
                return object;
            } else if (vop->varp()->vltype() == VLVT_UINT32) {
                *(reinterpret_cast<IData*>(vop->varDatap())) = vop->mask() & valuep->value.integer;
                return object;
            }
        }
        VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s",
                      __func__, VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
        return nullptr;
    } else if (const VerilatedVpioParam* const vop = VerilatedVpioParam::castp(object)) {
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Ignoring vpi_put_value to vpiParameter: %s",
                        __func__, vop->fullname());
        return nullptr;
    } else if (const VerilatedVpioConst* const vop = VerilatedVpioConst::castp(object)) {
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Ignoring vpi_put_value to vpiConstant: %s",
                        __func__, vop->fullname());
        return nullptr;
    }
    VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported vpiHandle (%p)", __func__, object);
    return nullptr;
}

void vpi_get_value_array(vpiHandle /*object*/, p_vpi_arrayvalue /*arrayvalue_p*/,
                         PLI_INT32* /*index_p*/, PLI_UINT32 /*num*/) {
    VL_VPI_UNIMP_();
}
void vpi_put_value_array(vpiHandle /*object*/, p_vpi_arrayvalue /*arrayvalue_p*/,
                         PLI_INT32* /*index_p*/, PLI_UINT32 /*num*/) {
    VL_VPI_UNIMP_();
}

// time processing

void vpi_get_time(vpiHandle object, p_vpi_time time_p) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!time_p)) {
        VL_VPI_WARNING_(__FILE__, __LINE__, "Ignoring vpi_get_time with nullptr value pointer");
        return;
    }
    if (time_p->type == vpiSimTime) {
        const QData qtime = VL_TIME_Q();
        VlWide<2> itime;
        VL_SET_WQ(itime, qtime);
        time_p->low = itime[0];
        time_p->high = itime[1];
        return;
    } else if (time_p->type == vpiScaledRealTime) {
        double dtime = VL_TIME_D();
        if (const VerilatedVpioScope* const vop = VerilatedVpioScope::castp(object)) {
            const int scalePow10
                = Verilated::threadContextp()->timeprecision() - vop->scopep()->timeunit();
            const double scale = vl_time_multiplier(scalePow10);  // e.g. 0.0001
            dtime *= scale;
        }
        time_p->real = dtime;
        return;
    }
    VL_VPI_ERROR_(__FILE__, __LINE__, "%s: Unsupported type (%d)", __func__, time_p->type);
}

// I/O routines

PLI_UINT32 vpi_mcd_open(PLI_BYTE8* filenamep) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    return VL_FOPEN_NN(filenamep, "wb");
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    VL_FCLOSE_I(mcd);
    return 0;
}

PLI_BYTE8* vpi_mcd_name(PLI_UINT32 /*mcd*/) {
    VL_VPI_UNIMP_();
    return nullptr;
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8* formatp, ...) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    va_list ap;
    va_start(ap, formatp);
    const int chars = vpi_mcd_vprintf(mcd, formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_printf(PLI_BYTE8* formatp, ...) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    va_list ap;
    va_start(ap, formatp);
    const int chars = vpi_vprintf(formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* formatp, va_list ap) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    return VL_VPRINTF(formatp, ap);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8* format, va_list ap) {
    VerilatedVpiImp::assertOneCheck();
    FILE* const fp = VL_CVT_I_FP(mcd);
    VL_VPI_ERROR_RESET_();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!fp)) return 0;
    const int chars = vfprintf(fp, format, ap);
    return chars;
}

PLI_INT32 vpi_flush(void) {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    Verilated::runFlushCallbacks();
    return 0;
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
    VerilatedVpiImp::assertOneCheck();
    FILE* const fp = VL_CVT_I_FP(mcd);
    VL_VPI_ERROR_RESET_();
    if (VL_UNLIKELY(!fp)) return 1;
    std::fflush(fp);
    return 0;
}

// utility routines

PLI_INT32 vpi_compare_objects(vpiHandle /*object1*/, vpiHandle /*object2*/) {
    VL_VPI_UNIMP_();
    return 0;
}
PLI_INT32 vpi_chk_error(p_vpi_error_info error_info_p) {
    // executing vpi_chk_error does not reset error
    // error_info_p can be nullptr, so only return level in that case
    VerilatedVpiImp::assertOneCheck();
    p_vpi_error_info const _error_info_p = VerilatedVpiImp::error_info()->getError();
    if (error_info_p && _error_info_p) *error_info_p = *_error_info_p;
    if (!_error_info_p) return 0;  // no error occured
    return _error_info_p->level;  // return error severity level
}

#ifndef VL_NO_LEGACY
PLI_INT32 vpi_free_object(vpiHandle object) {
    // vpi_free_object is IEEE deprecated, use vpi_release_handle
    return vpi_release_handle(object);
}
#endif

PLI_INT32 vpi_release_handle(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_release_handle %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpio* const vop = VerilatedVpio::castp(object);
    VL_VPI_ERROR_RESET_();
    if (VL_UNLIKELY(!vop)) return 0;
    VL_DO_DANGLING(delete vop, vop);
    return 1;
}

PLI_INT32 vpi_get_vlog_info(p_vpi_vlog_info vlog_info_p) VL_MT_SAFE {
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    const auto argc_argv = Verilated::threadContextp()->impp()->argc_argv();
    vlog_info_p->argc = argc_argv.first;
    vlog_info_p->argv = argc_argv.second;
    vlog_info_p->product = const_cast<PLI_BYTE8*>(Verilated::productName());
    vlog_info_p->version = const_cast<PLI_BYTE8*>(Verilated::productVersion());
    return 1;
}

// routines added with 1364-2001

PLI_INT32 vpi_get_data(PLI_INT32 /*id*/, PLI_BYTE8* /*dataLoc*/, PLI_INT32 /*numOfBytes*/) {
    VL_VPI_UNIMP_();
    return 0;
}
PLI_INT32 vpi_put_data(PLI_INT32 /*id*/, PLI_BYTE8* /*dataLoc*/, PLI_INT32 /*numOfBytes*/) {
    VL_VPI_UNIMP_();
    return 0;
}
void* vpi_get_userdata(vpiHandle /*obj*/) {
    VL_VPI_UNIMP_();
    return nullptr;
}
PLI_INT32 vpi_put_userdata(vpiHandle /*obj*/, void* /*userdata*/) {
    VL_VPI_UNIMP_();
    return 0;
}

PLI_INT32 vpi_control(PLI_INT32 operation, ...) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_control %d\n", operation););
    VerilatedVpiImp::assertOneCheck();
    VL_VPI_ERROR_RESET_();
    switch (operation) {
    case vpiFinish: {
        VL_FINISH_MT("", 0, "*VPI*");
        return 1;
    }
    case vpiStop: {
        VL_STOP_MT("", 0, "*VPI*");
        return 1;  // LCOV_EXCL_LINE
    }
    default: {
        VL_VPI_WARNING_(__FILE__, __LINE__, "%s: Unsupported type %s, ignoring", __func__,
                        VerilatedVpiError::strFromVpiProp(operation));
        return 0;
    }
    }
}

vpiHandle vpi_handle_by_multi_index(vpiHandle /*obj*/, PLI_INT32 /*num_index*/,
                                    PLI_INT32* /*index_array*/) {
    VL_VPI_UNIMP_();
    return nullptr;
}
