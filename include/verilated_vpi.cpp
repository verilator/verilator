// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilator: VPI implementation code
///
///     This file must be compiled and linked against all objects
///     created from Verilator or called by Verilator that use the VPI.
///
///     Use "verilator --vpi" to add this to the Makefile for the linker.
///
/// Code available from: https://verilator.org
///
//=========================================================================

#define _VERILATED_VPI_CPP_

#include "verilated.h"
#include "verilated_vpi.h"
#include "verilated_imp.h"

#include <list>
#include <map>
#include <set>

//======================================================================
// Internal constants

#define VL_DEBUG_IF_PLI VL_DEBUG_IF
constexpr unsigned VL_VPI_LINE_SIZE = 8192;

//======================================================================
// Internal macros

#define _VL_VPI_INTERNAL VerilatedVpiImp::error_info()->setMessage(vpiInternal)->setMessage
#define _VL_VPI_SYSTEM VerilatedVpiImp::error_info()->setMessage(vpiSystem)->setMessage
#define _VL_VPI_ERROR VerilatedVpiImp::error_info()->setMessage(vpiError)->setMessage
#define _VL_VPI_WARNING VerilatedVpiImp::error_info()->setMessage(vpiWarning)->setMessage
#define _VL_VPI_NOTICE VerilatedVpiImp::error_info()->setMessage(vpiNotice)->setMessage
#define _VL_VPI_ERROR_RESET VerilatedVpiImp::error_info()->resetError

// Not supported yet
#define _VL_VPI_UNIMP() \
    (_VL_VPI_ERROR(__FILE__, __LINE__, Verilated::catName("Unsupported VPI function: ", VL_FUNC)))

//======================================================================
// Implementation

// Base VPI handled object
class VerilatedVpio {
    // MEM MANGLEMENT
    static VL_THREAD_LOCAL vluint8_t* t_freeHead;

public:
    // CONSTRUCTORS
    VerilatedVpio() {}
    virtual ~VerilatedVpio() {}
    inline static void* operator new(size_t size) VL_MT_SAFE {
        // We new and delete tons of vpi structures, so keep them around
        // To simplify our free list, we use a size large enough for all derived types
        // We reserve word zero for the next pointer, as that's safer in case a
        // dangling reference to the original remains around.
        static const size_t chunk = 96;
        if (VL_UNCOVERABLE(size > chunk)) VL_FATAL_MT(__FILE__, __LINE__, "", "increase chunk");
        if (VL_LIKELY(t_freeHead)) {
            vluint8_t* newp = t_freeHead;
            t_freeHead = *(reinterpret_cast<vluint8_t**>(newp));
            return newp + 8;
        }
        // +8: 8 bytes for next
        vluint8_t* newp = reinterpret_cast<vluint8_t*>(::operator new(chunk + 8));
        return newp + 8;
    }
    inline static void operator delete(void* obj, size_t /*size*/)VL_MT_SAFE {
        vluint8_t* oldp = (static_cast<vluint8_t*>(obj)) - 8;
        *(reinterpret_cast<void**>(oldp)) = t_freeHead;
        t_freeHead = oldp;
    }
    // MEMBERS
    static inline VerilatedVpio* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpio*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    inline vpiHandle castVpiHandle() { return reinterpret_cast<vpiHandle>(this); }
    // ACCESSORS
    virtual const char* name() const { return "<null>"; }
    virtual const char* fullname() const { return "<null>"; }
    virtual const char* defname() const { return "<null>"; }
    virtual vluint32_t type() const { return 0; }
    virtual vluint32_t size() const { return 0; }
    virtual const VerilatedRange* rangep() const { return nullptr; }
    virtual vpiHandle dovpi_scan() { return 0; }
};

typedef PLI_INT32 (*VerilatedPliCb)(struct t_cb_data*);

class VerilatedVpioCb : public VerilatedVpio {
    t_cb_data m_cbData;
    s_vpi_value m_value;
    QData m_time;

public:
    // cppcheck-suppress uninitVar  // m_value
    VerilatedVpioCb(const t_cb_data* cbDatap, QData time)
        : m_cbData(*cbDatap)
        , m_time(time) {  // Need () or GCC 4.8 false warning
        m_value.format = cbDatap->value ? cbDatap->value->format : vpiSuppressVal;
        m_cbData.value = &m_value;
    }
    virtual ~VerilatedVpioCb() override {}
    static inline VerilatedVpioCb* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioCb*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiCallback; }
    vluint32_t reason() const { return m_cbData.reason; }
    VerilatedPliCb cb_rtnp() const { return m_cbData.cb_rtn; }
    t_cb_data* cb_datap() { return &(m_cbData); }
    QData time() const { return m_time; }
};

class VerilatedVpioConst : public VerilatedVpio {
    vlsint32_t m_num;

public:
    explicit VerilatedVpioConst(vlsint32_t num)
        : m_num{num} {}
    virtual ~VerilatedVpioConst() override {}
    static inline VerilatedVpioConst* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioConst*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiConstant; }
    vlsint32_t num() const { return m_num; }
};

class VerilatedVpioParam : public VerilatedVpio {
    const VerilatedVar* m_varp;
    const VerilatedScope* m_scopep;

public:
    VerilatedVpioParam(const VerilatedVar* varp, const VerilatedScope* scopep)
        : m_varp{varp}
        , m_scopep{scopep} {}

    virtual ~VerilatedVpioParam() override {}

    static inline VerilatedVpioParam* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioParam*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiParameter; }
    const VerilatedVar* varp() const { return m_varp; }
    void* varDatap() const { return m_varp->datap(); }
    const VerilatedScope* scopep() const { return m_scopep; }
    virtual const char* name() const override { return m_varp->name(); }
    virtual const char* fullname() const override {
        static VL_THREAD_LOCAL std::string out;
        out = std::string(m_scopep->name()) + "." + name();
        return out.c_str();
    }
};

class VerilatedVpioRange : public VerilatedVpio {
    const VerilatedRange* m_range;
    vlsint32_t m_iteration = 0;

public:
    explicit VerilatedVpioRange(const VerilatedRange* range)
        : m_range{range} {}
    virtual ~VerilatedVpioRange() override {}
    static inline VerilatedVpioRange* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioRange*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiRange; }
    virtual vluint32_t size() const override { return m_range->elements(); }
    virtual const VerilatedRange* rangep() const override { return m_range; }
    int iteration() const { return m_iteration; }
    void iterationInc() { ++m_iteration; }
    virtual vpiHandle dovpi_scan() override {
        if (!iteration()) {
            VerilatedVpioRange* nextp = new VerilatedVpioRange(*this);
            nextp->iterationInc();
            return ((nextp)->castVpiHandle());
        }
        return 0;  // End of list - only one deep
    }
};

class VerilatedVpioScope : public VerilatedVpio {
protected:
    const VerilatedScope* m_scopep;

public:
    explicit VerilatedVpioScope(const VerilatedScope* scopep)
        : m_scopep{scopep} {}
    virtual ~VerilatedVpioScope() override {}
    static inline VerilatedVpioScope* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioScope*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiScope; }
    const VerilatedScope* scopep() const { return m_scopep; }
    virtual const char* name() const override { return m_scopep->name(); }
    virtual const char* fullname() const override { return m_scopep->name(); }
};

class VerilatedVpioVar : public VerilatedVpio {
    const VerilatedVar* m_varp;
    const VerilatedScope* m_scopep;
    vluint8_t* m_prevDatap;  // Previous value of data, for cbValueChange
    union {
        vluint8_t u8[4];
        vluint32_t u32;
    } m_mask;  // memoized variable mask
    vluint32_t m_entSize;  // memoized variable size
protected:
    void* m_varDatap;  // varp()->datap() adjusted for array entries
    vlsint32_t m_index;
    const VerilatedRange& get_range() const {
        // Determine number of dimensions and return outermost
        return (m_varp->dims() > 1) ? m_varp->unpacked() : m_varp->packed();
    }

public:
    VerilatedVpioVar(const VerilatedVar* varp, const VerilatedScope* scopep)
        : m_varp{varp}
        , m_scopep{scopep}
        , m_index{0} {
        m_prevDatap = nullptr;
        m_mask.u32 = VL_MASK_I(varp->packed().elements());
        m_entSize = varp->entSize();
        m_varDatap = varp->datap();
    }
    virtual ~VerilatedVpioVar() override {
        if (m_prevDatap) VL_DO_CLEAR(delete[] m_prevDatap, m_prevDatap = nullptr);
    }
    static inline VerilatedVpioVar* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVar*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    const VerilatedVar* varp() const { return m_varp; }
    const VerilatedScope* scopep() const { return m_scopep; }
    vluint32_t mask() const { return m_mask.u32; }
    vluint8_t mask_byte(int idx) { return m_mask.u8[idx & 3]; }
    vluint32_t entSize() const { return m_entSize; }
    vluint32_t index() const { return m_index; }
    virtual vluint32_t type() const override {
        return (varp()->dims() > 1) ? vpiMemory : vpiReg;  // but might be wire, logic
    }
    virtual vluint32_t size() const override { return get_range().elements(); }
    virtual const VerilatedRange* rangep() const override { return &get_range(); }
    virtual const char* name() const override { return m_varp->name(); }
    virtual const char* fullname() const override {
        static VL_THREAD_LOCAL std::string out;
        out = std::string(m_scopep->name()) + "." + name();
        return out.c_str();
    }
    void* prevDatap() const { return m_prevDatap; }
    void* varDatap() const { return m_varDatap; }
    void createPrevDatap() {
        if (VL_UNLIKELY(!m_prevDatap)) {
            m_prevDatap = new vluint8_t[entSize()];
            memcpy(prevDatap(), varp()->datap(), entSize());
        }
    }
};

class VerilatedVpioMemoryWord : public VerilatedVpioVar {
public:
    VerilatedVpioMemoryWord(const VerilatedVar* varp, const VerilatedScope* scopep,
                            vlsint32_t index, int offset)
        : VerilatedVpioVar{varp, scopep} {
        m_index = index;
        m_varDatap = (static_cast<vluint8_t*>(varp->datap())) + entSize() * offset;
    }
    virtual ~VerilatedVpioMemoryWord() override {}
    static inline VerilatedVpioMemoryWord* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioMemoryWord*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiMemoryWord; }
    virtual vluint32_t size() const override { return varp()->packed().elements(); }
    virtual const VerilatedRange* rangep() const override { return &(varp()->packed()); }
    virtual const char* fullname() const override {
        static VL_THREAD_LOCAL std::string out;
        char num[20];
        sprintf(num, "%d", m_index);
        out = std::string(scopep()->name()) + "." + name() + "[" + num + "]";
        return out.c_str();
    }
};

class VerilatedVpioVarIter : public VerilatedVpio {
    const VerilatedScope* m_scopep;
    VerilatedVarNameMap::const_iterator m_it;
    bool m_started = false;

public:
    explicit VerilatedVpioVarIter(const VerilatedScope* scopep)
        : m_scopep{scopep} {}
    virtual ~VerilatedVpioVarIter() override {}
    static inline VerilatedVpioVarIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVarIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiIterator; }
    virtual vpiHandle dovpi_scan() override {
        if (VL_LIKELY(m_scopep->varsp())) {
            VerilatedVarNameMap* varsp = m_scopep->varsp();
            if (VL_UNLIKELY(!m_started)) {
                m_it = varsp->begin();
                m_started = true;
            } else if (VL_UNLIKELY(m_it == varsp->end())) {
                return 0;
            } else {
                ++m_it;
            }
            if (m_it == varsp->end()) return 0;
            return ((new VerilatedVpioVar(&(m_it->second), m_scopep))->castVpiHandle());
        }
        return 0;  // End of list - only one deep
    }
};

class VerilatedVpioMemoryWordIter : public VerilatedVpio {
    const vpiHandle m_handle;
    const VerilatedVar* m_varp;
    vlsint32_t m_iteration;
    vlsint32_t m_direction;
    bool m_done = false;

public:
    VerilatedVpioMemoryWordIter(const vpiHandle handle, const VerilatedVar* varp)
        : m_handle{handle}
        , m_varp{varp}
        , m_iteration{varp->unpacked().right()}
        , m_direction{VL_LIKELY(varp->unpacked().left() > varp->unpacked().right()) ? 1 : -1} {}
    virtual ~VerilatedVpioMemoryWordIter() override {}
    static inline VerilatedVpioMemoryWordIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioMemoryWordIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiIterator; }
    void iterationInc() {
        if (!(m_done = (m_iteration == m_varp->unpacked().left()))) m_iteration += m_direction;
    }
    virtual vpiHandle dovpi_scan() override {
        vpiHandle result;
        if (m_done) return 0;
        result = vpi_handle_by_index(m_handle, m_iteration);
        iterationInc();
        return result;
    }
};

class VerilatedVpioModule : public VerilatedVpioScope {
    const char* m_name;
    const char* m_fullname;

public:
    explicit VerilatedVpioModule(const VerilatedScope* modulep)
        : VerilatedVpioScope{modulep} {
        m_fullname = m_scopep->name();
        if (strncmp(m_fullname, "TOP.", 4) == 0) m_fullname += 4;
        m_name = m_scopep->identifier();
    }
    static inline VerilatedVpioModule* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioModule*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiModule; }
    virtual const char* name() const override { return m_name; }
    virtual const char* fullname() const override { return m_fullname; }
};

class VerilatedVpioModuleIter : public VerilatedVpio {
    const std::vector<const VerilatedScope*>* m_vec;
    std::vector<const VerilatedScope*>::const_iterator m_it;

public:
    explicit VerilatedVpioModuleIter(const std::vector<const VerilatedScope*>& vec)
        : m_vec{&vec} {
        m_it = m_vec->begin();
    }
    virtual ~VerilatedVpioModuleIter() override {}
    static inline VerilatedVpioModuleIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioModuleIter*>(reinterpret_cast<VerilatedVpio*>(h));
    }
    virtual vluint32_t type() const override { return vpiIterator; }
    virtual vpiHandle dovpi_scan() override {
        if (m_it == m_vec->end()) return 0;
        const VerilatedScope* modp = *m_it++;
        return (new VerilatedVpioModule(modp))->castVpiHandle();
    }
};

//======================================================================

struct VerilatedVpiTimedCbsCmp {
    /// Ordering sets keyed by time, then callback descriptor
    bool operator()(const std::pair<QData, VerilatedVpioCb*>& a,
                    const std::pair<QData, VerilatedVpioCb*>& b) const {
        if (a.first < b.first) return true;
        if (a.first > b.first) return false;
        return a.second < b.second;
    }
};

class VerilatedVpiError;

class VerilatedVpiImp {
    enum { CB_ENUM_MAX_VALUE = cbAtEndOfSimTime + 1 };  // Maxium callback reason
    typedef std::list<VerilatedVpioCb*> VpioCbList;
    typedef std::set<std::pair<QData, VerilatedVpioCb*>, VerilatedVpiTimedCbsCmp> VpioTimedCbs;

    struct product_info {
        PLI_BYTE8* product;
    };

    VpioCbList m_cbObjLists[CB_ENUM_MAX_VALUE];  // Callbacks for each supported reason
    VpioTimedCbs m_timedCbs;  // Time based callbacks
    VerilatedVpiError* m_errorInfop = nullptr;  // Container for vpi error info
    VerilatedAssertOneThread m_assertOne;  ///< Assert only called from single thread

    static VerilatedVpiImp s_s;  // Singleton

public:
    VerilatedVpiImp() {}
    ~VerilatedVpiImp() {}
    static void assertOneCheck() { s_s.m_assertOne.check(); }
    static void cbReasonAdd(VerilatedVpioCb* vop) {
        if (vop->reason() == cbValueChange) {
            if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
                varop->createPrevDatap();
            }
        }
        if (VL_UNCOVERABLE(vop->reason() >= CB_ENUM_MAX_VALUE)) {
            VL_FATAL_MT(__FILE__, __LINE__, "", "vpi bb reason too large");
        }
        s_s.m_cbObjLists[vop->reason()].push_back(vop);
    }
    static void cbTimedAdd(VerilatedVpioCb* vop) {
        s_s.m_timedCbs.insert(std::make_pair(vop->time(), vop));
    }
    static void cbReasonRemove(VerilatedVpioCb* cbp) {
        VpioCbList& cbObjList = s_s.m_cbObjLists[cbp->reason()];
        // We do not remove it now as we may be iterating the list,
        // instead set to nullptr and will cleanup later
        for (auto& ir : cbObjList) {
            if (ir == cbp) ir = nullptr;
        }
    }
    static void cbTimedRemove(VerilatedVpioCb* cbp) {
        const auto it = s_s.m_timedCbs.find(std::make_pair(cbp->time(), cbp));
        if (VL_LIKELY(it != s_s.m_timedCbs.end())) s_s.m_timedCbs.erase(it);
    }
    static void callTimedCbs() VL_MT_UNSAFE_ONE {
        assertOneCheck();
        QData time = VL_TIME_Q();
        for (auto it = s_s.m_timedCbs.begin(); it != s_s.m_timedCbs.end();) {
            if (VL_UNLIKELY(it->first <= time)) {
                VerilatedVpioCb* vop = it->second;
                const auto last_it = it;
                ++it;  // Timed callbacks are one-shot
                s_s.m_timedCbs.erase(last_it);
                VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: timed_callback %p\n", vop););
                (vop->cb_rtnp())(vop->cb_datap());
            } else {
                ++it;
            }
        }
    }
    static QData cbNextDeadline() {
        const auto it = s_s.m_timedCbs.cbegin();
        if (VL_LIKELY(it != s_s.m_timedCbs.cend())) return it->first;
        return ~0ULL;  // maxquad
    }
    static bool callCbs(vluint32_t reason) VL_MT_UNSAFE_ONE {
        VpioCbList& cbObjList = s_s.m_cbObjLists[reason];
        bool called = false;
        for (auto it = cbObjList.begin(); it != cbObjList.end();) {
            if (VL_UNLIKELY(!*it)) {  // Deleted earlier, cleanup
                it = cbObjList.erase(it);
                continue;
            }
            VerilatedVpioCb* vop = *it++;
            VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: reason_callback %d %p\n", reason, vop););
            (vop->cb_rtnp())(vop->cb_datap());
            called = true;
        }
        return called;
    }
    static bool callValueCbs() VL_MT_UNSAFE_ONE {
        assertOneCheck();
        VpioCbList& cbObjList = s_s.m_cbObjLists[cbValueChange];
        bool called = false;
        typedef std::set<VerilatedVpioVar*> VpioVarSet;
        VpioVarSet update;  // set of objects to update after callbacks
        for (auto it = cbObjList.begin(); it != cbObjList.end();) {
            if (VL_UNLIKELY(!*it)) {  // Deleted earlier, cleanup
                it = cbObjList.erase(it);
                continue;
            }
            VerilatedVpioCb* vop = *it++;
            if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
                void* newDatap = varop->varDatap();
                void* prevDatap = varop->prevDatap();  // Was malloced when we added the callback
                VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: value_test %s v[0]=%d/%d %p %p\n",
                                            varop->fullname(), *((CData*)newDatap),
                                            *((CData*)prevDatap), newDatap, prevDatap););
                if (memcmp(prevDatap, newDatap, varop->entSize()) != 0) {
                    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: value_callback %p %s v[0]=%d\n", vop,
                                                varop->fullname(), *((CData*)newDatap)););
                    update.insert(varop);
                    vpi_get_value(vop->cb_datap()->obj, vop->cb_datap()->value);
                    (vop->cb_rtnp())(vop->cb_datap());
                    called = true;
                }
            }
        }
        for (const auto& ip : update) { memcpy(ip->prevDatap(), ip->varDatap(), ip->entSize()); }
        return called;
    }

    static VerilatedVpiError* error_info() VL_MT_UNSAFE_ONE;  // getter for vpi error info
};

class VerilatedVpiError {
    //// Container for vpi error info

    t_vpi_error_info m_errorInfo;
    bool m_flag = false;
    char m_buff[VL_VPI_LINE_SIZE];
    void setError(PLI_BYTE8* message, PLI_BYTE8* code, PLI_BYTE8* file, PLI_INT32 line) {
        m_errorInfo.message = message;
        m_errorInfo.file = file;
        m_errorInfo.line = line;
        m_errorInfo.code = code;
        do_callbacks();
    }
    void do_callbacks() {
        if (getError()->level >= vpiError && Verilated::fatalOnVpiError()) {
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
    ~VerilatedVpiError() {}
    static void selfTest() VL_MT_UNSAFE_ONE;
    VerilatedVpiError* setMessage(PLI_INT32 level) {
        m_flag = true;
        m_errorInfo.level = level;
        return this;
    }
    void setMessage(const std::string& file, PLI_INT32 line, const char* message, ...) {
        // message cannot be a const string& as va_start cannot use a reference
        static VL_THREAD_LOCAL std::string filehold;
        va_list args;
        va_start(args, message);
        VL_VSNPRINTF(m_buff, sizeof(m_buff), message, args);
        va_end(args);
        m_errorInfo.state = vpiPLI;
        filehold = file;
        setError((PLI_BYTE8*)m_buff, nullptr, const_cast<PLI_BYTE8*>(filehold.c_str()), line);
    }
    p_vpi_error_info getError() {
        if (m_flag) return &m_errorInfo;
        return nullptr;
    }
    void resetError() { m_flag = false; }
    static void vpi_unsupported() {
        // Not supported yet
        p_vpi_error_info error_info_p = VerilatedVpiImp::error_info()->getError();
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

VerilatedVpiImp VerilatedVpiImp::s_s;  // Singleton
VL_THREAD_LOCAL vluint8_t* VerilatedVpio::t_freeHead = nullptr;

//======================================================================
// VerilatedVpi implementation

void VerilatedVpi::callTimedCbs() VL_MT_UNSAFE_ONE { VerilatedVpiImp::callTimedCbs(); }

bool VerilatedVpi::callValueCbs() VL_MT_UNSAFE_ONE { return VerilatedVpiImp::callValueCbs(); }

bool VerilatedVpi::callCbs(vluint32_t reason) VL_MT_UNSAFE_ONE {
    return VerilatedVpiImp::callCbs(reason);
}

QData VerilatedVpi::cbNextDeadline() VL_MT_UNSAFE_ONE { return VerilatedVpiImp::cbNextDeadline(); }

//======================================================================
// VerilatedVpiImp implementation

VerilatedVpiError* VerilatedVpiImp::error_info() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::assertOneCheck();
    if (VL_UNLIKELY(!s_s.m_errorInfop)) { s_s.m_errorInfop = new VerilatedVpiError(); }
    return s_s.m_errorInfop;
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
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
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
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "*undefined*",
        "vpiContAssignBit",
        "vpiNamedEventArray",
        "vpiIndexedPartSelect",
        "*undefined*",
        "*undefined*",
        "vpiGenScopeArray",
        "vpiGenScope",
        "vpiGenVar"
    };
    // clang-format on
    if (VL_UNCOVERABLE(vpiVal < 0)) return names[0];
    return names[(vpiVal <= vpiGenVar) ? vpiVal : 0];
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
    if (0 != strcmp((got), (exp))) { \
        std::string msg \
            = std::string("%Error: ") + "GOT = '" + got + "'" + "  EXP = '" + exp + "'"; \
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str()); \
    }

#define SELF_CHECK_ENUM_STR(fn, enumn) \
    do { \
        const char* strVal = VerilatedVpiError::fn(enumn); \
        SELF_CHECK_RESULT_CSTR(strVal, #enumn); \
    } while (0)

void VerilatedVpi::selfTest() VL_MT_UNSAFE_ONE { VerilatedVpiError::selfTest(); }
void VerilatedVpiError::selfTest() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::assertOneCheck();

    SELF_CHECK_ENUM_STR(strFromVpiVal, vpiBinStrVal);
    SELF_CHECK_ENUM_STR(strFromVpiVal, vpiRawFourStateVal);

    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAlways);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiWhile);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiAttribute);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiUdpArray);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiContAssignBit);
    SELF_CHECK_ENUM_STR(strFromVpiObjType, vpiGenVar);

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
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!cb_data_p)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s : callback data pointer is null", VL_FUNC);
        return nullptr;
    }
    switch (cb_data_p->reason) {
    case cbAfterDelay: {
        QData time = 0;
        if (cb_data_p->time) time = _VL_SET_QII(cb_data_p->time->high, cb_data_p->time->low);
        VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, VL_TIME_Q() + time);
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_register_cb %d %p delay=%" VL_PRI64 "u\n",
                                    cb_data_p->reason, vop, time););
        VerilatedVpiImp::cbTimedAdd(vop);
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
        VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, 0);
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_register_cb %d %p\n", cb_data_p->reason, vop););
        VerilatedVpiImp::cbReasonAdd(vop);
        return vop->castVpiHandle();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported callback type %s", VL_FUNC,
                        VerilatedVpiError::strFromVpiCallbackReason(cb_data_p->reason));
        return nullptr;
    }
}

PLI_INT32 vpi_remove_cb(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_remove_cb %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpioCb* vop = VerilatedVpioCb::castp(object);
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!vop)) return 0;
    if (vop->cb_datap()->reason == cbAfterDelay) {
        VerilatedVpiImp::cbTimedRemove(vop);
    } else {
        VerilatedVpiImp::cbReasonRemove(vop);
    }
    return 1;
}

void vpi_get_cb_info(vpiHandle /*object*/, p_cb_data /*cb_data_p*/) { _VL_VPI_UNIMP(); }
vpiHandle vpi_register_systf(p_vpi_systf_data /*systf_data_p*/) {
    _VL_VPI_UNIMP();
    return 0;
}
void vpi_get_systf_info(vpiHandle /*object*/, p_vpi_systf_data /*systf_data_p*/) {
    _VL_VPI_UNIMP();
}

// for obtaining handles

vpiHandle vpi_handle_by_name(PLI_BYTE8* namep, vpiHandle scope) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!namep)) return nullptr;
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle_by_name %s %p\n", namep, scope););
    const VerilatedVar* varp = nullptr;
    const VerilatedScope* scopep;
    VerilatedVpioScope* voScopep = VerilatedVpioScope::castp(scope);
    std::string scopeAndName = namep;
    if (voScopep) {
        scopeAndName = std::string(voScopep->fullname()) + "." + namep;
        namep = const_cast<PLI_BYTE8*>(scopeAndName.c_str());
    }
    {
        // This doesn't yet follow the hierarchy in the proper way
        scopep = Verilated::scopeFind(namep);
        if (scopep) {  // Whole thing found as a scope
            if (scopep->type() == VerilatedScope::SCOPE_MODULE) {
                return (new VerilatedVpioModule(scopep))->castVpiHandle();
            } else {
                return (new VerilatedVpioScope(scopep))->castVpiHandle();
            }
        }
        const char* baseNamep = scopeAndName.c_str();
        std::string scopename;
        const char* dotp = strrchr(namep, '.');
        if (VL_LIKELY(dotp)) {
            baseNamep = dotp + 1;
            scopename = std::string(namep, dotp - namep);
        }

        if (scopename.find('.') == std::string::npos) {
            // This is a toplevel, hence search in our TOP ports first.
            scopep = Verilated::scopeFind("TOP");
            if (scopep) { varp = scopep->varFind(baseNamep); }
        }
        if (!varp) {
            scopep = Verilated::scopeFind(scopename.c_str());
            if (!scopep) return nullptr;
            varp = scopep->varFind(baseNamep);
        }
    }
    if (!varp) return nullptr;

    if (varp->isParam()) {
        return (new VerilatedVpioParam(varp, scopep))->castVpiHandle();
    } else {
        return (new VerilatedVpioVar(varp, scopep))->castVpiHandle();
    }
}

vpiHandle vpi_handle_by_index(vpiHandle object, PLI_INT32 indx) {
    // Used to get array entries
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle_by_index %p %d\n", object, indx););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpioVar* varop = VerilatedVpioVar::castp(object);
    _VL_VPI_ERROR_RESET();
    if (VL_LIKELY(varop)) {
        if (varop->varp()->dims() < 2) return 0;
        if (VL_LIKELY(varop->varp()->unpacked().left() >= varop->varp()->unpacked().right())) {
            if (VL_UNLIKELY(indx > varop->varp()->unpacked().left()
                            || indx < varop->varp()->unpacked().right()))
                return 0;
            return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
                                                indx - varop->varp()->unpacked().right()))
                ->castVpiHandle();
        }
        if (VL_UNLIKELY(indx < varop->varp()->unpacked().left()
                        || indx > varop->varp()->unpacked().right()))
            return 0;
        return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
                                            indx - varop->varp()->unpacked().left()))
            ->castVpiHandle();
    }
    _VL_VPI_INTERNAL(__FILE__, __LINE__, "%s : can't resolve handle", VL_FUNC);
    return 0;
}

// for traversing relationships

vpiHandle vpi_handle(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle %d %p\n", type, object););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    switch (type) {
    case vpiLeftRange: {
        if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return 0;
            return (new VerilatedVpioConst(vop->rangep()->left()))->castVpiHandle();
        } else if (VerilatedVpioRange* vop = VerilatedVpioRange::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return 0;
            return (new VerilatedVpioConst(vop->rangep()->left()))->castVpiHandle();
        }
        _VL_VPI_WARNING(__FILE__, __LINE__,
                        "%s: Unsupported vpiHandle (%p) for type %s, nothing will be returned",
                        VL_FUNC, object, VerilatedVpiError::strFromVpiMethod(type));
        return 0;
    }
    case vpiRightRange: {
        if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return 0;
            return (new VerilatedVpioConst(vop->rangep()->right()))->castVpiHandle();
        } else if (VerilatedVpioRange* vop = VerilatedVpioRange::castp(object)) {
            if (VL_UNLIKELY(!vop->rangep())) return 0;
            return (new VerilatedVpioConst(vop->rangep()->right()))->castVpiHandle();
        }
        _VL_VPI_WARNING(__FILE__, __LINE__,
                        "%s: Unsupported vpiHandle (%p) for type %s, nothing will be returned",
                        VL_FUNC, object, VerilatedVpiError::strFromVpiMethod(type));
        return 0;
    }
    case vpiIndex: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return (new VerilatedVpioConst(vop->index()))->castVpiHandle();
    }
    case vpiScope: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return (new VerilatedVpioScope(vop->scopep()))->castVpiHandle();
    }
    case vpiParent: {
        VerilatedVpioMemoryWord* vop = VerilatedVpioMemoryWord::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return (new VerilatedVpioVar(vop->varp(), vop->scopep()))->castVpiHandle();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        VL_FUNC, VerilatedVpiError::strFromVpiMethod(type));
        return 0;
    }
}

vpiHandle vpi_handle_multi(PLI_INT32 /*type*/, vpiHandle /*refHandle1*/, vpiHandle /*refHandle2*/,
                           ...) {
    _VL_VPI_UNIMP();
    return 0;
}

vpiHandle vpi_iterate(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_iterate %d %p\n", type, object););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    switch (type) {
    case vpiMemoryWord: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        if (vop->varp()->dims() < 2) return 0;
        if (vop->varp()->dims() > 2) {
            _VL_VPI_WARNING(__FILE__, __LINE__,
                            "%s: %s, object %s has unsupported number of indices (%d)", VL_FUNC,
                            VerilatedVpiError::strFromVpiMethod(type), vop->fullname(),
                            vop->varp()->dims());
        }
        return (new VerilatedVpioMemoryWordIter(object, vop->varp()))->castVpiHandle();
    }
    case vpiRange: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        if (vop->varp()->dims() < 2) return 0;
        // Unsupported is multidim list
        if (vop->varp()->dims() > 2) {
            _VL_VPI_WARNING(__FILE__, __LINE__,
                            "%s: %s, object %s has unsupported number of indices (%d)", VL_FUNC,
                            VerilatedVpiError::strFromVpiMethod(type), vop->fullname(),
                            vop->varp()->dims());
        }
        return ((new VerilatedVpioRange(vop->rangep()))->castVpiHandle());
    }
    case vpiReg: {
        VerilatedVpioScope* vop = VerilatedVpioScope::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return ((new VerilatedVpioVarIter(vop->scopep()))->castVpiHandle());
    }
    case vpiModule: {
        VerilatedVpioModule* vop = VerilatedVpioModule::castp(object);
        const VerilatedHierarchyMap* map = VerilatedImp::hierarchyMap();
        const VerilatedScope* mod = vop ? vop->scopep() : nullptr;
        const auto it = vlstd::as_const(map)->find(const_cast<VerilatedScope*>(mod));
        if (it == map->end()) return 0;
        return ((new VerilatedVpioModuleIter(it->second))->castVpiHandle());
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        VL_FUNC, VerilatedVpiError::strFromVpiObjType(type));
        return 0;
    }
}
vpiHandle vpi_scan(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_scan %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    if (VL_UNLIKELY(!vop)) return nullptr;
    return vop->dovpi_scan();
}

// for processing properties

PLI_INT32 vpi_get(PLI_INT32 property, vpiHandle object) {
    // Leave this in the header file - in many cases the compiler can constant propagate "object"
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get %d %p\n", property, object););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    switch (property) {
    case vpiTimePrecision: {
        return Verilated::timeprecision();
    }
    case vpiTimeUnit: {
        VerilatedVpioScope* vop = VerilatedVpioScope::castp(object);
        if (!vop) return Verilated::timeunit();  // Null asks for global, not unlikely
        return vop->scopep()->timeunit();
    }
    case vpiType: {
        VerilatedVpio* vop = VerilatedVpio::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return vop->type();
    }
    case vpiDirection: {
        // By forthought, the directions already are vpi enumerated
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return vop->varp()->vldir();
    }
    case vpiScalar:  // FALLTHRU
    case vpiVector: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return (property == vpiVector) ^ (vop->varp()->dims() == 0);
    }
    case vpiSize: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return vop->size();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        VL_FUNC, VerilatedVpiError::strFromVpiProp(property));
        return 0;
    }
}

PLI_INT64 vpi_get64(PLI_INT32 /*property*/, vpiHandle /*object*/) {
    _VL_VPI_UNIMP();
    return 0;
}

PLI_BYTE8* vpi_get_str(PLI_INT32 property, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get_str %d %p\n", property, object););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET();
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
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        VL_FUNC, VerilatedVpiError::strFromVpiProp(property));
        return 0;
    }
}

// delay processing

void vpi_get_delays(vpiHandle /*object*/, p_vpi_delay /*delay_p*/) { _VL_VPI_UNIMP(); }
void vpi_put_delays(vpiHandle /*object*/, p_vpi_delay /*delay_p*/) { _VL_VPI_UNIMP(); }

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
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s", VL_FUNC,
                  VerilatedVpiError::strFromVpiVal(valuep->format), fullname);
    return status;
}

void vl_get_value(const VerilatedVar* varp, void* varDatap, p_vpi_value valuep,
                  const char* fullname) {
    if (!vl_check_format(varp, valuep, fullname, true)) return;
    // Maximum required size is for binary string, one byte per bit plus null termination
    static VL_THREAD_LOCAL char outStr[1 + VL_MULS_MAX_WORDS * 32];
    // cppcheck-suppress variableScope
    static VL_THREAD_LOCAL int outStrSz = sizeof(outStr) - 1;
    // We used to presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
    // This may cause backward compatibility issues with older code.
    if (valuep->format == vpiVectorVal) {
        // Vector pointer must come from our memory pool
        // It only needs to persist until the next vpi_get_value
        static VL_THREAD_LOCAL t_vpi_vecval out[VL_MULS_MAX_WORDS * 2];
        valuep->value.vector = out;
        if (varp->vltype() == VLVT_UINT8) {
            out[0].aval = *(reinterpret_cast<CData*>(varDatap));
            out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_UINT16) {
            out[0].aval = *(reinterpret_cast<SData*>(varDatap));
            out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_UINT32) {
            out[0].aval = *(reinterpret_cast<IData*>(varDatap));
            out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_UINT64) {
            QData data = *(reinterpret_cast<QData*>(varDatap));
            out[1].aval = static_cast<IData>(data >> 32ULL);
            out[1].bval = 0;
            out[0].aval = static_cast<IData>(data);
            out[0].bval = 0;
            return;
        } else if (varp->vltype() == VLVT_WDATA) {
            int words = VL_WORDS_I(varp->packed().elements());
            if (VL_UNCOVERABLE(words >= VL_MULS_MAX_WORDS)) {
                VL_FATAL_MT(
                    __FILE__, __LINE__, "",
                    "vpi_get_value with more than VL_MULS_MAX_WORDS; increase and recompile");
            }
            WDataInP datap = (reinterpret_cast<EData*>(varDatap));
            for (int i = 0; i < words; ++i) {
                out[i].aval = datap[i];
                out[i].bval = 0;
            }
            return;
        }
    } else if (valuep->format == vpiBinStrVal) {
        valuep->value.str = outStr;
        int bits = varp->packed().elements();
        CData* datap = (reinterpret_cast<CData*>(varDatap));
        int i;
        if (bits > outStrSz) {
            // limit maximum size of output to size of buffer to prevent overrun.
            bits = outStrSz;
            _VL_VPI_WARNING(
                __FILE__, __LINE__,
                "%s: Truncating string value of %s for %s"
                " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                VL_FUNC, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, outStrSz,
                VL_MULS_MAX_WORDS, bits);
        }
        for (i = 0; i < bits; ++i) {
            char val = (datap[i >> 3] >> (i & 7)) & 1;
            outStr[bits - i - 1] = val ? '1' : '0';
        }
        outStr[i] = '\0';
        return;
    } else if (valuep->format == vpiOctStrVal) {
        valuep->value.str = outStr;
        int chars = (varp->packed().elements() + 2) / 3;
        int bytes = VL_BYTES_I(varp->packed().elements());
        CData* datap = (reinterpret_cast<CData*>(varDatap));
        int i;
        if (chars > outStrSz) {
            // limit maximum size of output to size of buffer to prevent overrun.
            _VL_VPI_WARNING(
                __FILE__, __LINE__,
                "%s: Truncating string value of %s for %s"
                " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                VL_FUNC, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, outStrSz,
                VL_MULS_MAX_WORDS, chars);
            chars = outStrSz;
        }
        for (i = 0; i < chars; ++i) {
            div_t idx = div(i * 3, 8);
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
                unsigned int rem = varp->packed().elements() % 3;
                if (rem) {
                    // generate bit mask & zero non existant bits
                    val &= (1 << rem) - 1;
                }
            }
            outStr[chars - i - 1] = '0' + (val & 7);
        }
        outStr[i] = '\0';
        return;
    } else if (valuep->format == vpiDecStrVal) {
        valuep->value.str = outStr;
        // outStrSz does not include nullptr termination so add one
        if (varp->vltype() == VLVT_UINT8) {
            VL_SNPRINTF(outStr, outStrSz + 1, "%hhu",
                        static_cast<unsigned char>(*(reinterpret_cast<CData*>(varDatap))));
            return;
        } else if (varp->vltype() == VLVT_UINT16) {
            VL_SNPRINTF(outStr, outStrSz + 1, "%hu",
                        static_cast<unsigned short>(*(reinterpret_cast<SData*>(varDatap))));
            return;
        } else if (varp->vltype() == VLVT_UINT32) {
            VL_SNPRINTF(outStr, outStrSz + 1, "%u",
                        static_cast<unsigned int>(*(reinterpret_cast<IData*>(varDatap))));
            return;
        } else if (varp->vltype() == VLVT_UINT64) {
            VL_SNPRINTF(outStr, outStrSz + 1, "%llu",
                        static_cast<unsigned long long>(*(reinterpret_cast<QData*>(varDatap))));
            return;
        }
    } else if (valuep->format == vpiHexStrVal) {
        valuep->value.str = outStr;
        int chars = (varp->packed().elements() + 3) >> 2;
        CData* datap = (reinterpret_cast<CData*>(varDatap));
        int i;
        if (chars > outStrSz) {
            // limit maximum size of output to size of buffer to prevent overrun.
            _VL_VPI_WARNING(
                __FILE__, __LINE__,
                "%s: Truncating string value of %s for %s"
                " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                VL_FUNC, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, outStrSz,
                VL_MULS_MAX_WORDS, chars);
            chars = outStrSz;
        }
        for (i = 0; i < chars; ++i) {
            char val = (datap[i >> 1] >> ((i & 1) << 2)) & 15;
            if (i == (chars - 1)) {
                // most signifcant char, mask off non existant bits when vector
                // size is not a multiple of 4
                unsigned int rem = varp->packed().elements() & 3;
                if (rem) {
                    // generate bit mask & zero non existant bits
                    val &= (1 << rem) - 1;
                }
            }
            outStr[chars - i - 1] = "0123456789abcdef"[static_cast<int>(val)];
        }
        outStr[i] = '\0';
        return;
    } else if (valuep->format == vpiStringVal) {
        if (varp->vltype() == VLVT_STRING) {
            valuep->value.str = reinterpret_cast<char*>(varDatap);
            return;
        } else {
            valuep->value.str = outStr;
            int bytes = VL_BYTES_I(varp->packed().elements());
            CData* datap = (reinterpret_cast<CData*>(varDatap));
            int i;
            if (bytes > outStrSz) {
                // limit maximum size of output to size of buffer to prevent overrun.
                _VL_VPI_WARNING(
                    __FILE__, __LINE__,
                    "%s: Truncating string value of %s for %s"
                    " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                    VL_FUNC, VerilatedVpiError::strFromVpiVal(valuep->format), fullname, outStrSz,
                    VL_MULS_MAX_WORDS, bytes);
                bytes = outStrSz;
            }
            for (i = 0; i < bytes; ++i) {
                char val = datap[bytes - i - 1];
                // other simulators replace [leading?] zero chars with spaces, replicate here.
                outStr[i] = val ? val : ' ';
            }
            outStr[i] = '\0';
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
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s", VL_FUNC,
                  VerilatedVpiError::strFromVpiVal(valuep->format), fullname);
}

void vpi_get_value(vpiHandle object, p_vpi_value valuep) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get_value %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!valuep)) return;

    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
        vl_get_value(vop->varp(), vop->varDatap(), valuep, vop->fullname());
        return;
    } else if (VerilatedVpioParam* vop = VerilatedVpioParam::castp(object)) {
        vl_get_value(vop->varp(), vop->varDatap(), valuep, vop->fullname());
        return;
    } else if (VerilatedVpioConst* vop = VerilatedVpioConst::castp(object)) {
        if (valuep->format == vpiIntVal) {
            valuep->value.integer = vop->num();
            return;
        }
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s", VL_FUNC,
                      VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
        return;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported vpiHandle (%p)", VL_FUNC, object);
}

vpiHandle vpi_put_value(vpiHandle object, p_vpi_value valuep, p_vpi_time /*time_p*/,
                        PLI_INT32 /*flags*/) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_put_value %p %p\n", object, valuep););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!valuep)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_put_value with nullptr value pointer");
        return 0;
    }
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
        VL_DEBUG_IF_PLI(
            VL_DBG_MSGF("- vpi:   vpi_put_value name=%s fmt=%d vali=%d\n", vop->fullname(),
                        valuep->format, valuep->value.integer);
            VL_DBG_MSGF("- vpi:   varp=%p  putatp=%p\n", vop->varp()->datap(), vop->varDatap()););

        if (VL_UNLIKELY(!vop->varp()->isPublicRW())) {
            _VL_VPI_WARNING(__FILE__, __LINE__,
                            "Ignoring vpi_put_value to signal marked read-only,"
                            " use public_flat_rw instead: %s",
                            vop->fullname());
            return 0;
        }
        if (!vl_check_format(vop->varp(), valuep, vop->fullname(), false)) return 0;
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
                *(reinterpret_cast<QData*>(vop->varDatap())) = _VL_SET_QII(
                    valuep->value.vector[1].aval & vop->mask(), valuep->value.vector[0].aval);
                return object;
            } else if (vop->varp()->vltype() == VLVT_WDATA) {
                int words = VL_WORDS_I(vop->varp()->packed().elements());
                WDataOutP datap = (reinterpret_cast<EData*>(vop->varDatap()));
                for (int i = 0; i < words; ++i) {
                    datap[i] = valuep->value.vector[i].aval;
                    if (i == (words - 1)) datap[i] &= vop->mask();
                }
                return object;
            }
        } else if (valuep->format == vpiBinStrVal) {
            int bits = vop->varp()->packed().elements();
            int len = strlen(valuep->value.str);
            CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
            for (int i = 0; i < bits; ++i) {
                char set = (i < len) ? (valuep->value.str[len - i - 1] == '1') : 0;
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
            int chars = (vop->varp()->packed().elements() + 2) / 3;
            int bytes = VL_BYTES_I(vop->varp()->packed().elements());
            int len = strlen(valuep->value.str);
            CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
            div_t idx;
            datap[0] = 0;  // reset zero'th byte
            for (int i = 0; i < chars; ++i) {
                union {
                    char byte[2];
                    vluint16_t half;
                } val;
                idx = div(i * 3, 8);
                if (i < len) {
                    // ignore illegal chars
                    char digit = valuep->value.str[len - i - 1];
                    if (digit >= '0' && digit <= '7') {
                        val.half = digit - '0';
                    } else {
                        _VL_VPI_WARNING(__FILE__, __LINE__,
                                        "%s: Non octal character '%c' in '%s' as value %s for %s",
                                        VL_FUNC, digit, valuep->value.str,
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
            int success = sscanf(valuep->value.str, "%30llu%15s", &val, remainder);
            if (success < 1) {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Parsing failed for '%s' as value %s for %s",
                              VL_FUNC, valuep->value.str,
                              VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
                return 0;
            }
            if (success > 1) {
                _VL_VPI_WARNING(__FILE__, __LINE__,
                                "%s: Trailing garbage '%s' in '%s' as value %s for %s", VL_FUNC,
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
            int chars = (vop->varp()->packed().elements() + 3) >> 2;
            CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
            char* val = valuep->value.str;
            // skip hex ident if one is detected at the start of the string
            if (val[0] == '0' && (val[1] == 'x' || val[1] == 'X')) val += 2;
            int len = strlen(val);
            for (int i = 0; i < chars; ++i) {
                char hex;
                // compute hex digit value
                if (i < len) {
                    char digit = val[len - i - 1];
                    if (digit >= '0' && digit <= '9') {
                        hex = digit - '0';
                    } else if (digit >= 'a' && digit <= 'f') {
                        hex = digit - 'a' + 10;
                    } else if (digit >= 'A' && digit <= 'F') {
                        hex = digit - 'A' + 10;
                    } else {
                        _VL_VPI_WARNING(__FILE__, __LINE__,
                                        "%s: Non hex character '%c' in '%s' as value %s for %s",
                                        VL_FUNC, digit, valuep->value.str,
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
            int bytes = VL_BYTES_I(vop->varp()->packed().elements());
            int len = strlen(valuep->value.str);
            CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
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
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s",
                      VL_FUNC, VerilatedVpiError::strFromVpiVal(valuep->format), vop->fullname());
        return nullptr;
    } else if (VerilatedVpioParam* vop = VerilatedVpioParam::castp(object)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Ignoring vpi_put_value to vpiParameter: %s",
                        VL_FUNC, vop->fullname());
        return 0;
    } else if (VerilatedVpioConst* vop = VerilatedVpioConst::castp(object)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Ignoring vpi_put_value to vpiConstant: %s",
                        VL_FUNC, vop->fullname());
        return 0;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported vpiHandle (%p)", VL_FUNC, object);
    return nullptr;
}

void vpi_get_value_array(vpiHandle /*object*/, p_vpi_arrayvalue /*arrayvalue_p*/,
                         PLI_INT32* /*index_p*/, PLI_UINT32 /*num*/) {
    _VL_VPI_UNIMP();
}
void vpi_put_value_array(vpiHandle /*object*/, p_vpi_arrayvalue /*arrayvalue_p*/,
                         PLI_INT32* /*index_p*/, PLI_UINT32 /*num*/) {
    _VL_VPI_UNIMP();
}

// time processing

void vpi_get_time(vpiHandle object, p_vpi_time time_p) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!time_p)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_get_time with nullptr value pointer");
        return;
    }
    if (time_p->type == vpiSimTime) {
        QData qtime = VL_TIME_Q();
        WData itime[2];
        VL_SET_WQ(itime, qtime);
        time_p->low = itime[0];
        time_p->high = itime[1];
        return;
    } else if (time_p->type == vpiScaledRealTime) {
        double dtime = VL_TIME_D();
        if (VerilatedVpioScope* vop = VerilatedVpioScope::castp(object)) {
            int scalePow10 = Verilated::timeprecision() - vop->scopep()->timeunit();
            double scale = vl_time_multiplier(scalePow10);  // e.g. 0.0001
            dtime *= scale;
        }
        time_p->real = dtime;
        return;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported type (%d)", VL_FUNC, time_p->type);
}

// I/O routines

PLI_UINT32 vpi_mcd_open(PLI_BYTE8* filenamep) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    return VL_FOPEN_NN(filenamep, "wb");
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    VL_FCLOSE_I(mcd);
    return 0;
}

PLI_BYTE8* vpi_mcd_name(PLI_UINT32 /*mcd*/) {
    _VL_VPI_UNIMP();
    return 0;
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8* formatp, ...) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    va_list ap;
    va_start(ap, formatp);
    int chars = vpi_mcd_vprintf(mcd, formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_printf(PLI_BYTE8* formatp, ...) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    va_list ap;
    va_start(ap, formatp);
    int chars = vpi_vprintf(formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* formatp, va_list ap) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    return VL_VPRINTF(formatp, ap);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8* format, va_list ap) {
    VerilatedVpiImp::assertOneCheck();
    FILE* fp = VL_CVT_I_FP(mcd);
    _VL_VPI_ERROR_RESET();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!fp)) return 0;
    int chars = vfprintf(fp, format, ap);
    return chars;
}

PLI_INT32 vpi_flush(void) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    Verilated::runFlushCallbacks();
    return 0;
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
    VerilatedVpiImp::assertOneCheck();
    FILE* fp = VL_CVT_I_FP(mcd);
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!fp)) return 1;
    fflush(fp);
    return 0;
}

// utility routines

PLI_INT32 vpi_compare_objects(vpiHandle /*object1*/, vpiHandle /*object2*/) {
    _VL_VPI_UNIMP();
    return 0;
}
PLI_INT32 vpi_chk_error(p_vpi_error_info error_info_p) {
    // executing vpi_chk_error does not reset error
    // error_info_p can be nullptr, so only return level in that case
    VerilatedVpiImp::assertOneCheck();
    p_vpi_error_info _error_info_p = VerilatedVpiImp::error_info()->getError();
    if (error_info_p && _error_info_p) *error_info_p = *_error_info_p;
    if (!_error_info_p) return 0;  // no error occured
    return _error_info_p->level;  // return error severity level
}

PLI_INT32 vpi_free_object(vpiHandle object) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    return vpi_release_handle(object);  // Deprecated
}

PLI_INT32 vpi_release_handle(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_release_handle %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!vop)) return 0;
    vpi_remove_cb(object);  // May not be a callback, but that's ok
    VL_DO_DANGLING(delete vop, vop);
    return 1;
}

PLI_INT32 vpi_get_vlog_info(p_vpi_vlog_info vlog_info_p) VL_MT_SAFE {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    vlog_info_p->argc = Verilated::getCommandArgs()->argc;
    vlog_info_p->argv = const_cast<PLI_BYTE8**>(Verilated::getCommandArgs()->argv);
    vlog_info_p->product = const_cast<PLI_BYTE8*>(Verilated::productName());
    vlog_info_p->version = const_cast<PLI_BYTE8*>(Verilated::productVersion());
    return 1;
}

// routines added with 1364-2001

PLI_INT32 vpi_get_data(PLI_INT32 /*id*/, PLI_BYTE8* /*dataLoc*/, PLI_INT32 /*numOfBytes*/) {
    _VL_VPI_UNIMP();
    return 0;
}
PLI_INT32 vpi_put_data(PLI_INT32 /*id*/, PLI_BYTE8* /*dataLoc*/, PLI_INT32 /*numOfBytes*/) {
    _VL_VPI_UNIMP();
    return 0;
}
void* vpi_get_userdata(vpiHandle /*obj*/) {
    _VL_VPI_UNIMP();
    return 0;
}
PLI_INT32 vpi_put_userdata(vpiHandle /*obj*/, void* /*userdata*/) {
    _VL_VPI_UNIMP();
    return 0;
}

PLI_INT32 vpi_control(PLI_INT32 operation, ...) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_control %d\n", operation););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
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
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, ignoring", VL_FUNC,
                        VerilatedVpiError::strFromVpiProp(operation));
        return 0;
    }
    }
}

vpiHandle vpi_handle_by_multi_index(vpiHandle /*obj*/, PLI_INT32 /*num_index*/,
                                    PLI_INT32* /*index_array*/) {
    _VL_VPI_UNIMP();
    return 0;
}
