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

#if VM_SC
# include "verilated_sc.h"
#endif
#include "verilated.h"
#include "verilated_vpi.h"
#include "verilated_imp.h"

#include <list>
#include <map>
#include <set>
#include <sstream>

//======================================================================
// Internal constants

#define VL_DEBUG_IF_PLI VL_DEBUG_IF
#define VL_VPI_LINE_SIZE 8192

//======================================================================
// Internal macros

#define _VL_VPI_INTERNAL    VerilatedVpiImp::error_info()->setMessage(vpiInternal)->setMessage
#define _VL_VPI_SYSTEM      VerilatedVpiImp::error_info()->setMessage(vpiSystem  )->setMessage
#define _VL_VPI_ERROR       VerilatedVpiImp::error_info()->setMessage(vpiError   )->setMessage
#define _VL_VPI_WARNING     VerilatedVpiImp::error_info()->setMessage(vpiWarning )->setMessage
#define _VL_VPI_NOTICE      VerilatedVpiImp::error_info()->setMessage(vpiNotice  )->setMessage
#define _VL_VPI_ERROR_RESET VerilatedVpiImp::error_info()->resetError

// Not supported yet
#define _VL_VPI_UNIMP() \
    _VL_VPI_ERROR(__FILE__, __LINE__, Verilated::catName("Unsupported VPI function: ", VL_FUNC));

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
        if (VL_UNCOVERABLE(size>chunk)) VL_FATAL_MT(__FILE__, __LINE__, "", "increase chunk");
        if (VL_LIKELY(t_freeHead)) {
            vluint8_t* newp = t_freeHead;
            t_freeHead = *((vluint8_t**)newp);
            return newp+8;
        }
        // +8: 8 bytes for next
        vluint8_t* newp = reinterpret_cast<vluint8_t*>(::operator new(chunk+8));
        return newp+8;
    }
    inline static void operator delete(void* obj, size_t size) VL_MT_SAFE {
        vluint8_t* oldp = ((vluint8_t*)obj)-8;
        *((void**)oldp) = t_freeHead;
        t_freeHead = oldp;
    }
    // MEMBERS
    static inline VerilatedVpio* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpio*>((VerilatedVpio*)h); }
    inline vpiHandle castVpiHandle() { return reinterpret_cast<vpiHandle>(this); }
    // ACCESSORS
    virtual const char* name() const { return "<null>"; }
    virtual const char* fullname() const { return "<null>"; }
    virtual const char* defname() const { return "<null>"; }
    virtual vluint32_t type() const { return 0; }
    virtual vluint32_t size() const { return 0; }
    virtual const VerilatedRange* rangep() const { return NULL; }
    virtual vpiHandle dovpi_scan() { return 0; }
};

typedef PLI_INT32 (*VerilatedPliCb)(struct t_cb_data *);

class VerilatedVpioCb : public VerilatedVpio {
    t_cb_data           m_cbData;
    s_vpi_value         m_value;
    QData               m_time;
public:
    // cppcheck-suppress uninitVar  // m_value
    VerilatedVpioCb(const t_cb_data* cbDatap, QData time)
        : m_cbData(*cbDatap), m_time(time) {
        m_value.format = cbDatap->value ? cbDatap->value->format : vpiSuppressVal;
        m_cbData.value = &m_value;
    }
    virtual ~VerilatedVpioCb() {}
    static inline VerilatedVpioCb* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioCb*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiCallback; }
    vluint32_t reason() const { return m_cbData.reason; }
    VerilatedPliCb cb_rtnp() const { return m_cbData.cb_rtn; }
    t_cb_data* cb_datap() { return &(m_cbData); }
    QData time() const { return m_time; }
};

class VerilatedVpioConst : public VerilatedVpio {
    vlsint32_t          m_num;
public:
    explicit VerilatedVpioConst(vlsint32_t num) : m_num(num) {}
    virtual ~VerilatedVpioConst() {}
    static inline VerilatedVpioConst* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioConst*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiUndefined; }
    vlsint32_t num() const { return m_num; }
};

class VerilatedVpioRange : public VerilatedVpio {
    const VerilatedRange* m_range;
    vlsint32_t m_iteration;
public:
    explicit VerilatedVpioRange(const VerilatedRange* range) : m_range(range), m_iteration(0) {}
    virtual ~VerilatedVpioRange() {}
    static inline VerilatedVpioRange* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioRange*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiRange; }
    virtual vluint32_t size() const { return m_range->elements(); }
    virtual const VerilatedRange* rangep() const { return m_range; }
    int iteration() const { return m_iteration; }
    void iterationInc() { ++m_iteration; }
    virtual vpiHandle dovpi_scan() {
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
    const VerilatedScope*       m_scopep;
public:
    explicit VerilatedVpioScope(const VerilatedScope* scopep)
        : m_scopep(scopep) {}
    virtual ~VerilatedVpioScope() {}
    static inline VerilatedVpioScope* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioScope*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiScope; }
    const VerilatedScope* scopep() const { return m_scopep; }
    virtual const char* name() const { return m_scopep->name(); }
    virtual const char* fullname() const { return m_scopep->name(); }
};

class VerilatedVpioVar : public VerilatedVpio {
    const VerilatedVar*         m_varp;
    const VerilatedScope*       m_scopep;
    vluint8_t*                  m_prevDatap;    // Previous value of data, for cbValueChange
    union {
        vluint8_t u8[4];
        vluint32_t u32;
    } m_mask;                                   // memoized variable mask
    vluint32_t                  m_entSize;      // memoized variable size
protected:
    void*                       m_varDatap;     // varp()->datap() adjusted for array entries
    vlsint32_t                  m_index;
    const VerilatedRange& get_range() const {
        // Determine number of dimensions and return outermost
        return (m_varp->dims()>1) ? m_varp->unpacked() : m_varp->packed();
    }
public:
    VerilatedVpioVar(const VerilatedVar* varp, const VerilatedScope* scopep)
        : m_varp(varp), m_scopep(scopep), m_index(0) {
        m_prevDatap = NULL;
        m_mask.u32 = VL_MASK_I(varp->packed().elements());
        m_entSize = varp->entSize();
        m_varDatap = varp->datap();
    }
    virtual ~VerilatedVpioVar() {
        if (m_prevDatap) { delete [] m_prevDatap; m_prevDatap = NULL; }
    }
    static inline VerilatedVpioVar* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVar*>((VerilatedVpio*)h); }
    const VerilatedVar* varp() const { return m_varp; }
    const VerilatedScope* scopep() const { return m_scopep; }
    vluint32_t mask() const { return m_mask.u32; }
    vluint8_t mask_byte(int idx) { return m_mask.u8[idx & 3]; }
    vluint32_t entSize() const { return m_entSize; }
    vluint32_t index() { return m_index; }
    virtual vluint32_t type() const {
      return (varp()->dims()>1) ? vpiMemory : vpiReg;  // but might be wire, logic
    }
    virtual vluint32_t size() const { return get_range().elements(); }
    virtual const VerilatedRange* rangep() const { return &get_range(); }
    virtual const char* name() const { return m_varp->name(); }
    virtual const char* fullname() const {
        static VL_THREAD_LOCAL std::string out;
        out = std::string(m_scopep->name())+"."+name();
        return out.c_str();
    }
    void* prevDatap() const { return m_prevDatap; }
    void* varDatap() const { return m_varDatap; }
    void createPrevDatap() {
        if (VL_UNLIKELY(!m_prevDatap)) {
            m_prevDatap = new vluint8_t [entSize()];
            memcpy(prevDatap(), varp()->datap(), entSize());
        }
    }
};

class VerilatedVpioMemoryWord : public VerilatedVpioVar {
public:
    VerilatedVpioMemoryWord(const VerilatedVar* varp, const VerilatedScope* scopep,
                            vlsint32_t index, int offset)
        : VerilatedVpioVar(varp, scopep) {
        m_index = index;
        m_varDatap = ((vluint8_t*)varp->datap()) + entSize()*offset;
    }
    virtual ~VerilatedVpioMemoryWord() {}
    static inline VerilatedVpioMemoryWord* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioMemoryWord*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiMemoryWord; }
    virtual  vluint32_t size() const { return varp()->packed().elements(); }
    virtual const VerilatedRange* rangep() const { return &(varp()->packed()); }
    virtual const char* fullname() const {
        static VL_THREAD_LOCAL std::string out;
        char num[20]; sprintf(num, "%d", m_index);
        out = std::string(scopep()->name())+"."+name()+"["+num+"]";
        return out.c_str();
    }
};

class VerilatedVpioVarIter : public VerilatedVpio {
    const VerilatedScope*       m_scopep;
    VerilatedVarNameMap::const_iterator m_it;
    bool m_started;
public:
    explicit VerilatedVpioVarIter(const VerilatedScope* scopep)
        : m_scopep(scopep), m_started(false) {  }
    virtual ~VerilatedVpioVarIter() {}
    static inline VerilatedVpioVarIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioVarIter*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiIterator; }
    virtual vpiHandle dovpi_scan() {
        if (VL_LIKELY(m_scopep->varsp())) {
            VerilatedVarNameMap* varsp = m_scopep->varsp();
            if (VL_UNLIKELY(!m_started)) { m_it = varsp->begin(); m_started=true; }
            else if (VL_UNLIKELY(m_it == varsp->end())) return 0;
            else ++m_it;
            if (m_it == varsp->end()) return 0;
            return ((new VerilatedVpioVar(&(m_it->second), m_scopep))
                    ->castVpiHandle());
        }
        return 0;  // End of list - only one deep
    }
};

class VerilatedVpioMemoryWordIter : public VerilatedVpio {
    const vpiHandle             m_handle;
    const VerilatedVar*         m_varp;
    vlsint32_t                  m_iteration;
    vlsint32_t                  m_direction;
    bool                        m_done;
public:
    VerilatedVpioMemoryWordIter(const vpiHandle handle, const VerilatedVar* varp)
        : m_handle(handle), m_varp(varp), m_iteration(varp->unpacked().right()),
          m_direction(VL_LIKELY(varp->unpacked().left() > varp->unpacked().right())
                      ? 1 : -1),
          m_done(false) { }
    virtual ~VerilatedVpioMemoryWordIter() {}
    static inline VerilatedVpioMemoryWordIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioMemoryWordIter*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiIterator; }
    void iterationInc() {
        if (!(m_done = (m_iteration == m_varp->unpacked().left()))) {
            m_iteration += m_direction;
        }
    }
    virtual vpiHandle dovpi_scan() {
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
            : VerilatedVpioScope(modulep) {
        m_fullname = m_scopep->name();
        if (strncmp(m_fullname, "TOP.", 4) == 0) m_fullname += 4;
        m_name = m_scopep->identifier();
    }
    static inline VerilatedVpioModule* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioModule*>((VerilatedVpio*)h); }
    virtual vluint32_t type() const { return vpiModule; }
    virtual const char* name() const { return m_name; }
    virtual const char* fullname() const { return m_fullname; }
};

class VerilatedVpioModuleIter : public VerilatedVpio {
    const std::vector<const VerilatedScope*> *m_vec;
    std::vector<const VerilatedScope*>::const_iterator m_it;
public:
    explicit VerilatedVpioModuleIter(const std::vector<const VerilatedScope*>& vec) : m_vec(&vec) {
        m_it = m_vec->begin();
    }
    virtual ~VerilatedVpioModuleIter() {}
    static inline VerilatedVpioModuleIter* castp(vpiHandle h) {
        return dynamic_cast<VerilatedVpioModuleIter*>((VerilatedVpio*) h); }
    virtual vluint32_t type() const { return vpiIterator; }
    virtual vpiHandle dovpi_scan() {
        if (m_it == m_vec->end()) {
            return 0;
        }
        const VerilatedScope* modp = *m_it++;
        return (new VerilatedVpioModule(modp))->castVpiHandle();
    }
};

//======================================================================

struct VerilatedVpiTimedCbsCmp {
    /// Ordering sets keyed by time, then callback descriptor
    bool operator()(const std::pair<QData,VerilatedVpioCb*>& a,
                    const std::pair<QData,VerilatedVpioCb*>& b) const {
        if (a.first < b.first) return 1;
        if (a.first > b.first) return 0;
        return a.second < b.second;
    }
};

class VerilatedVpiError;

class VerilatedVpiImp {
    enum { CB_ENUM_MAX_VALUE = cbAtEndOfSimTime+1 };  // Maxium callback reason
    typedef std::list<VerilatedVpioCb*> VpioCbList;
    typedef std::set<std::pair<QData,VerilatedVpioCb*>,VerilatedVpiTimedCbsCmp > VpioTimedCbs;

    struct product_info {
        PLI_BYTE8* product;
    };

    VpioCbList          m_cbObjLists[CB_ENUM_MAX_VALUE];  // Callbacks for each supported reason
    VpioTimedCbs        m_timedCbs;  // Time based callbacks
    VerilatedVpiError*  m_errorInfop;  // Container for vpi error info
    VerilatedAssertOneThread m_assertOne;  ///< Assert only called from single thread

    static VerilatedVpiImp s_s;  // Singleton

public:
    VerilatedVpiImp() { m_errorInfop=NULL; }
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
        // instead set to NULL and will cleanup later
        for (VpioCbList::iterator it=cbObjList.begin(); it!=cbObjList.end(); ++it) {
            if (*it == cbp) *it = NULL;
        }
    }
    static void cbTimedRemove(VerilatedVpioCb* cbp) {
        VpioTimedCbs::iterator it=s_s.m_timedCbs.find(std::make_pair(cbp->time(), cbp));
        if (VL_LIKELY(it != s_s.m_timedCbs.end())) {
            s_s.m_timedCbs.erase(it);
        }
    }
    static void callTimedCbs() VL_MT_UNSAFE_ONE {
        assertOneCheck();
        QData time = VL_TIME_Q();
        for (VpioTimedCbs::iterator it=s_s.m_timedCbs.begin(); it!=s_s.m_timedCbs.end(); ) {
            if (VL_UNLIKELY(it->first <= time)) {
                VerilatedVpioCb* vop = it->second;
                VpioTimedCbs::iterator last_it = it;
                ++it;  // Timed callbacks are one-shot
                s_s.m_timedCbs.erase(last_it);
                VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: timed_callback %p\n", vop););
                (vop->cb_rtnp()) (vop->cb_datap());
            }
            else { ++it; }
        }
    }
    static QData cbNextDeadline() {
        VpioTimedCbs::const_iterator it=s_s.m_timedCbs.begin();
        if (VL_LIKELY(it != s_s.m_timedCbs.end())) {
            return it->first;
        }
        return ~VL_ULL(0);  // maxquad
    }
    static bool callCbs(vluint32_t reason) VL_MT_UNSAFE_ONE {
        VpioCbList& cbObjList = s_s.m_cbObjLists[reason];
        bool called = false;
        for (VpioCbList::iterator it=cbObjList.begin(); it!=cbObjList.end();) {
            if (VL_UNLIKELY(!*it)) {  // Deleted earlier, cleanup
                it = cbObjList.erase(it);
                continue;
            }
            VerilatedVpioCb* vop = *it++;
            VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: reason_callback %d %p\n", reason, vop););
            (vop->cb_rtnp()) (vop->cb_datap());
            called = true;
        }
        return called;
    }
    static void callValueCbs() VL_MT_UNSAFE_ONE {
        assertOneCheck();
        VpioCbList& cbObjList = s_s.m_cbObjLists[cbValueChange];
        typedef std::set<VerilatedVpioVar*> VpioVarSet;
        VpioVarSet update;  // set of objects to update after callbacks
        for (VpioCbList::iterator it=cbObjList.begin(); it!=cbObjList.end();) {
            if (VL_UNLIKELY(!*it)) {  // Deleted earlier, cleanup
                it = cbObjList.erase(it);
                continue;
            }
            VerilatedVpioCb* vop = *it++;
            if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
                void* newDatap = varop->varDatap();
                void* prevDatap = varop->prevDatap();  // Was malloced when we added the callback
                VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: value_test %s v[0]=%d/%d %p %p\n",
                                            varop->fullname(),
                                            *((CData*)newDatap), *((CData*)prevDatap),
                                            newDatap, prevDatap););
                if (memcmp(prevDatap, newDatap, varop->entSize())) {
                    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: value_callback %p %s v[0]=%d\n",
                                                vop, varop->fullname(), *((CData*)newDatap)););
                    update.insert(varop);
                    vpi_get_value(vop->cb_datap()->obj, vop->cb_datap()->value);
                    (vop->cb_rtnp()) (vop->cb_datap());
                }
            }
        }
        for (VpioVarSet::const_iterator it=update.begin(); it!=update.end(); ++it) {
            memcpy((*it)->prevDatap(), (*it)->varDatap(), (*it)->entSize());
        }
    }

    static VerilatedVpiError* error_info() VL_MT_UNSAFE_ONE;  // getter for vpi error info
};

class VerilatedVpiError {
    //// Container for vpi error info

    t_vpi_error_info m_errorInfo;
    bool m_flag;
    char m_buff[VL_VPI_LINE_SIZE];
    void setError(PLI_BYTE8 *message, PLI_BYTE8 *code, PLI_BYTE8 *file, PLI_INT32 line) {
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

    VerilatedVpiError() : m_flag(false) {
        m_buff[0] = '\0';
        m_errorInfo.product = (PLI_BYTE8*)Verilated::productName();
    }
    ~VerilatedVpiError() {}
    static void selfTest() VL_MT_UNSAFE_ONE;
    VerilatedVpiError* setMessage(PLI_INT32 level) {
        m_flag = true;
        m_errorInfo.level = level;
        return this;
    }
    void setMessage(std::string file, PLI_INT32 line, const char* message, ...) {
        // message cannot be a const string& as va_start cannot use a reference
        static VL_THREAD_LOCAL std::string filehold;
        va_list args;
        va_start(args, message);
        VL_VSNPRINTF(m_buff, sizeof(m_buff), message, args);
        va_end(args);
        m_errorInfo.state = vpiPLI;
        filehold = file;
        setError((PLI_BYTE8*)m_buff, NULL, (PLI_BYTE8*)filehold.c_str(), line);
    }
    p_vpi_error_info getError() {
        if (m_flag) return &m_errorInfo;
        return NULL;
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
VL_THREAD_LOCAL vluint8_t* VerilatedVpio::t_freeHead = NULL;

//======================================================================
// VerilatedVpi implementation

void VerilatedVpi::callTimedCbs() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::callTimedCbs();
}

void VerilatedVpi::callValueCbs() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::callValueCbs();
}

bool VerilatedVpi::callCbs(vluint32_t reason) VL_MT_UNSAFE_ONE {
    return VerilatedVpiImp::callCbs(reason);
}

//======================================================================
// VerilatedVpiImp implementation

VerilatedVpiError* VerilatedVpiImp::error_info() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::assertOneCheck();
    if (VL_UNLIKELY(!s_s.m_errorInfop)) {
        s_s.m_errorInfop = new VerilatedVpiError();
    }
    return s_s.m_errorInfop;
}

//======================================================================
// VerilatedVpiError Methods

const char* VerilatedVpiError::strFromVpiVal(PLI_INT32 vpiVal) VL_MT_SAFE {
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
    if (vpiVal < 0) return names[0];
    return names[(vpiVal<=vpiRawFourStateVal) ? vpiVal : 0];
}
const char* VerilatedVpiError::strFromVpiObjType(PLI_INT32 vpiVal) VL_MT_SAFE {
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
    if (vpiVal < 0) return names[0];
    return names[(vpiVal<=vpiGenVar) ? vpiVal : 0];
}
const char* VerilatedVpiError::strFromVpiMethod(PLI_INT32 vpiVal) VL_MT_SAFE {
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
    if (vpiVal>vpiStmt || vpiVal<vpiCondition) {
        return "*undefined*";
    }
    return names[vpiVal-vpiCondition];
}

const char* VerilatedVpiError::strFromVpiCallbackReason(PLI_INT32 vpiVal) VL_MT_SAFE {
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
    if (vpiVal < 0) return names[0];
    return names[(vpiVal<=cbAtEndOfSimTime) ? vpiVal : 0];
}

const char* VerilatedVpiError::strFromVpiProp(PLI_INT32 vpiVal) VL_MT_SAFE {
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
    if (vpiVal == vpiUndefined) {
      return "vpiUndefined";
    }
    return names[(vpiVal<=vpiIsProtected) ? vpiVal : 0];
}

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        std::string msg = std::string("%Error: ")   \
             + "GOT = '"+((got)?(got):"<null>")+"'"  \
             + "  EXP = '"+((exp)?(exp):"<null>")+"'";  \
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());  \
    }

#define CHECK_ENUM_STR(fn, enum) \
    do { \
        const char* strVal = VerilatedVpiError::fn(enum);       \
        CHECK_RESULT_CSTR(strVal, #enum); \
    } while (0)

void VerilatedVpi::selfTest() VL_MT_UNSAFE_ONE {
    VerilatedVpiError::selfTest();
}
void VerilatedVpiError::selfTest() VL_MT_UNSAFE_ONE {
    VerilatedVpiImp::assertOneCheck();

    CHECK_ENUM_STR(strFromVpiVal, vpiBinStrVal);
    CHECK_ENUM_STR(strFromVpiVal, vpiRawFourStateVal);

    CHECK_ENUM_STR(strFromVpiObjType, vpiAlways);
    CHECK_ENUM_STR(strFromVpiObjType, vpiWhile);
    CHECK_ENUM_STR(strFromVpiObjType, vpiAttribute);
    CHECK_ENUM_STR(strFromVpiObjType, vpiUdpArray);
    CHECK_ENUM_STR(strFromVpiObjType, vpiContAssignBit);
    CHECK_ENUM_STR(strFromVpiObjType, vpiGenVar);

    CHECK_ENUM_STR(strFromVpiMethod, vpiCondition);
    CHECK_ENUM_STR(strFromVpiMethod, vpiStmt);

    CHECK_ENUM_STR(strFromVpiCallbackReason, cbValueChange);
    CHECK_ENUM_STR(strFromVpiCallbackReason, cbAtEndOfSimTime);

    CHECK_ENUM_STR(strFromVpiProp, vpiType);
    CHECK_ENUM_STR(strFromVpiProp, vpiProtected);
    CHECK_ENUM_STR(strFromVpiProp, vpiDirection);
    CHECK_ENUM_STR(strFromVpiProp, vpiTermIndex);
    CHECK_ENUM_STR(strFromVpiProp, vpiConstType);
    CHECK_ENUM_STR(strFromVpiProp, vpiAutomatic);
    CHECK_ENUM_STR(strFromVpiProp, vpiOffset);
    CHECK_ENUM_STR(strFromVpiProp, vpiStop);
    CHECK_ENUM_STR(strFromVpiProp, vpiIsProtected);
}

#undef CHECK_ENUM_STR
#undef CHECK_RESULT_CSTR

//======================================================================
// callback related

vpiHandle vpi_register_cb(p_cb_data cb_data_p) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!cb_data_p)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s : callback data pointer is null", VL_FUNC);
        return NULL;
    }
    switch (cb_data_p->reason) {
    case cbAfterDelay: {
        QData time = 0;
        if (cb_data_p->time) time = _VL_SET_QII(cb_data_p->time->high, cb_data_p->time->low);
        VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, VL_TIME_Q()+time);
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_register_cb %d %p delay=%" VL_PRI64 "u\n",
                                    cb_data_p->reason, vop, time););
        VerilatedVpiImp::cbTimedAdd(vop);
        return vop->castVpiHandle();
    }
    case cbReadWriteSynch:            // FALLTHRU // Supported via vlt_main.cpp
    case cbReadOnlySynch:             // FALLTHRU // Supported via vlt_main.cpp
    case cbNextSimTime:               // FALLTHRU // Supported via vlt_main.cpp
    case cbStartOfSimulation:         // FALLTHRU // Supported via vlt_main.cpp
    case cbEndOfSimulation:           // FALLTHRU // Supported via vlt_main.cpp
    case cbValueChange:               // FALLTHRU // Supported via vlt_main.cpp
    case cbPLIError:                  // FALLTHRU // NOP, but need to return handle, so make object
    case cbEnterInteractive:          // FALLTHRU // NOP, but need to return handle, so make object
    case cbExitInteractive:           // FALLTHRU // NOP, but need to return handle, so make object
    case cbInteractiveScopeChange: {  // FALLTHRU // NOP, but need to return handle, so make object
        VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, 0);
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_register_cb %d %p\n", cb_data_p->reason, vop););
        VerilatedVpiImp::cbReasonAdd(vop);
        return vop->castVpiHandle();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported callback type %s",
                        VL_FUNC, VerilatedVpiError::strFromVpiCallbackReason(cb_data_p->reason));
        return NULL;
    };
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

void vpi_get_cb_info(vpiHandle object, p_cb_data cb_data_p) {
    _VL_VPI_UNIMP(); return;
}
vpiHandle vpi_register_systf(p_vpi_systf_data systf_data_p) {
    _VL_VPI_UNIMP(); return 0;
}
void vpi_get_systf_info(vpiHandle object, p_vpi_systf_data systf_data_p) {
    _VL_VPI_UNIMP(); return;
}

// for obtaining handles

vpiHandle vpi_handle_by_name(PLI_BYTE8* namep, vpiHandle scope) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!namep)) return NULL;
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle_by_name %s %p\n", namep, scope););
    const VerilatedVar* varp = NULL;
    const VerilatedScope* scopep;
    VerilatedVpioScope* voScopep = VerilatedVpioScope::castp(scope);
    std::string scopeAndName = namep;
    if (voScopep) {
        scopeAndName = std::string(voScopep->fullname()) + "." + namep;
        namep = (PLI_BYTE8*)scopeAndName.c_str();
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
            baseNamep = dotp+1;
            scopename = std::string(namep, dotp-namep);
        }

        if (scopename.find(".") == std::string::npos) {
            // This is a toplevel, hence search in our TOP ports first.
            scopep = Verilated::scopeFind("TOP");
            if (scopep) {
                varp = scopep->varFind(baseNamep);
            }
        }
        if (!varp) {
            scopep = Verilated::scopeFind(scopename.c_str());
            if (!scopep) return NULL;
            varp = scopep->varFind(baseNamep);
        }
    }
    if (!varp) return NULL;
    return (new VerilatedVpioVar(varp, scopep))->castVpiHandle();
}

vpiHandle vpi_handle_by_index(vpiHandle object, PLI_INT32 indx) {
    // Used to get array entries
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_handle_by_index %p %d\n", object, indx););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpioVar* varop = VerilatedVpioVar::castp(object);
    _VL_VPI_ERROR_RESET();
    if (VL_LIKELY(varop)) {
        if (varop->varp()->dims()<2) return 0;
        if (VL_LIKELY(varop->varp()->unpacked().left() >= varop->varp()->unpacked().right())) {
            if (VL_UNLIKELY(indx > varop->varp()->unpacked().left()
                            || indx < varop->varp()->unpacked().right())) return 0;
            return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
                                              indx - varop->varp()->unpacked().right()))
                ->castVpiHandle();
        }
        if (VL_UNLIKELY(indx < varop->varp()->unpacked().left()
                        || indx > varop->varp()->unpacked().right())) return 0;
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
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        if (VL_UNLIKELY(!vop->rangep())) return 0;
        return (new VerilatedVpioConst(vop->rangep()->left()))->castVpiHandle();
    }
    case vpiRightRange: {
        VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        if (VL_UNLIKELY(!vop->rangep())) return 0;
        return (new VerilatedVpioConst(vop->rangep()->right()))->castVpiHandle();
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

vpiHandle vpi_handle_multi(PLI_INT32 type, vpiHandle refHandle1, vpiHandle refHandle2, ... ) {
    _VL_VPI_UNIMP(); return 0;
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
                            "%s: %s, object %s has unsupported number of indices (%d)",
                            VL_FUNC, VerilatedVpiError::strFromVpiMethod(type),
                            vop->fullname() , vop->varp()->dims());
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
                            "%s: %s, object %s has unsupported number of indices (%d)",
                            VL_FUNC, VerilatedVpiError::strFromVpiMethod(type),
                            vop->fullname() , vop->varp()->dims());
        }
        return ((new VerilatedVpioRange(vop->rangep()))->castVpiHandle());
    }
    case vpiReg: {
        VerilatedVpioScope* vop = VerilatedVpioScope::castp(object);
        if (VL_UNLIKELY(!vop)) return 0;
        return ((new VerilatedVpioVarIter(vop->scopep()))
                ->castVpiHandle());
    }
    case vpiModule: {
        VerilatedVpioModule* vop = VerilatedVpioModule::castp(object);
        const VerilatedHierarchyMap* map = VerilatedImp::hierarchyMap();
        const VerilatedScope *mod = vop ? vop->scopep() : NULL;
        VerilatedHierarchyMap::const_iterator it = map->find((VerilatedScope*) mod);
        if (it == map->end()) return 0;
        return  ((new VerilatedVpioModuleIter(it->second))->castVpiHandle());
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
    if (VL_UNLIKELY(!vop)) return NULL;
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
        return VL_TIME_PRECISION;
    }
    case vpiTimeUnit: {
        return VL_TIME_UNIT;
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
        return (property==vpiVector) ^ (vop->varp()->dims()==0);
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

PLI_INT64 vpi_get64(PLI_INT32 property, vpiHandle object) {
    _VL_VPI_UNIMP();
    return 0;
}

PLI_BYTE8 *vpi_get_str(PLI_INT32 property, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get_str %d %p\n", property, object););
    VerilatedVpiImp::assertOneCheck();
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!vop)) return NULL;
    switch (property) {
    case vpiName: {
        return (PLI_BYTE8*)vop->name();
    }
    case vpiFullName: {
        return (PLI_BYTE8*)vop->fullname();
    }
    case vpiDefName: {
        return (PLI_BYTE8*)vop->defname();
    }
    case vpiType: {
        return (PLI_BYTE8*) VerilatedVpiError::strFromVpiObjType(vop->type());
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
                        VL_FUNC, VerilatedVpiError::strFromVpiProp(property));
        return 0;
    }
}

// delay processing

void vpi_get_delays(vpiHandle object, p_vpi_delay delay_p) {
    _VL_VPI_UNIMP();
    return;
}
void vpi_put_delays(vpiHandle object, p_vpi_delay delay_p) {
    _VL_VPI_UNIMP();
    return;
}

// value processing

void vpi_get_value(vpiHandle object, p_vpi_value value_p) {
    // Maximum required size is for binary string, one byte per bit plus null termination
    static VL_THREAD_LOCAL char outStr[1+VL_MULS_MAX_WORDS*32];
    // cppcheck-suppress variableScope
    static VL_THREAD_LOCAL int outStrSz = sizeof(outStr)-1;
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_get_value %p\n", object););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!value_p)) return;
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
        // We used to presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
        // This may cause backward compatability issues with older code.
        if (value_p->format == vpiVectorVal) {
            // Vector pointer must come from our memory pool
            // It only needs to persist until the next vpi_get_value
            static VL_THREAD_LOCAL t_vpi_vecval out[VL_MULS_MAX_WORDS*2];
            value_p->value.vector = out;
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
                out[0].aval = *(reinterpret_cast<CData*>(vop->varDatap()));
                out[0].bval = 0;
                return;
            case VLVT_UINT16:
                out[0].aval = *(reinterpret_cast<SData*>(vop->varDatap()));
                out[0].bval = 0;
                return;
            case VLVT_UINT32:
                out[0].aval = *(reinterpret_cast<IData*>(vop->varDatap()));
                out[0].bval = 0;
                return;
            case VLVT_WDATA: {
                int words = VL_WORDS_I(vop->varp()->packed().elements());
                if (VL_UNCOVERABLE(words >= VL_MULS_MAX_WORDS)) {
                    VL_FATAL_MT(__FILE__, __LINE__, "",
                                "vpi_get_value with more than VL_MULS_MAX_WORDS; increase and recompile");
                }
                WDataInP datap = (reinterpret_cast<EData*>(vop->varDatap()));
                for (int i=0; i<words; ++i) {
                    out[i].aval = datap[i];
                    out[i].bval = 0;
                }
                return;
            }
            case VLVT_UINT64: {
                QData data = *(reinterpret_cast<QData*>(vop->varDatap()));
                out[1].aval = static_cast<IData>(data>>VL_ULL(32));
                out[1].bval = 0;
                out[0].aval = static_cast<IData>(data);
                out[0].bval = 0;
                return;
            }
            default: {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return;
            }
            }
        } else if (value_p->format == vpiBinStrVal) {
            value_p->value.str = outStr;
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int bits = vop->varp()->packed().elements();
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                int i;
                if (bits > outStrSz) {
                  // limit maximum size of output to size of buffer to prevent overrun.
                  bits = outStrSz;
                  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s"
                                  " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                                  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                                  vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, bits);
                }
                for (i=0; i<bits; ++i) {
                    char val = (datap[i>>3]>>(i&7))&1;
                    outStr[bits-i-1] = val?'1':'0';
                }
                outStr[i] = '\0';
                return;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return;
            }
        } else if (value_p->format == vpiOctStrVal) {
            value_p->value.str = outStr;
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int chars = (vop->varp()->packed().elements()+2)/3;
                int bytes = VL_BYTES_I(vop->varp()->packed().elements());
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                int i;
                if (chars > outStrSz) {
                    // limit maximum size of output to size of buffer to prevent overrun.
                    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s"
                                    " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                                    VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                                    vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, chars);
                    chars = outStrSz;
                }
                for (i=0; i<chars; ++i) {
                    div_t idx = div(i*3, 8);
                    int val = datap[idx.quot];
                    if ((idx.quot+1)<bytes) {
                        // if the next byte is valid or that in
                        // for when the required 3 bits straddle adjacent bytes
                        val |= datap[idx.quot+1]<<8;
                    }
                    // align so least significant 3 bits represent octal char
                    val >>= idx.rem;
                    if (i==(chars-1)) {
                        // most signifcant char, mask off non existant bits when vector
                        // size is not a multiple of 3
                        unsigned int rem = vop->varp()->packed().elements() % 3;
                        if (rem) {
                            // generate bit mask & zero non existant bits
                            val &= (1<<rem)-1;
                        }
                    }
                    outStr[chars-i-1] = '0' + (val&7);
                }
                outStr[i] = '\0';
                return;
            }
            default:
                strcpy(outStr, "0");
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return;
            }
        } else if (value_p->format == vpiDecStrVal) {
            value_p->value.str = outStr;
            switch (vop->varp()->vltype()) {
            // outStrSz does not include NULL termination so add one
            case VLVT_UINT8:
                VL_SNPRINTF(outStr, outStrSz+1, "%hhu",
                            static_cast<unsigned char>(*(reinterpret_cast<CData*>(vop->varDatap()))));
                return;
            case VLVT_UINT16:
                VL_SNPRINTF(outStr, outStrSz+1, "%hu",
                            static_cast<unsigned short>(*(reinterpret_cast<SData*>(vop->varDatap()))));
                return;
            case VLVT_UINT32:
                VL_SNPRINTF(outStr, outStrSz+1, "%u",
                            static_cast<unsigned int>(*(reinterpret_cast<IData*>(vop->varDatap()))));
                return;
            case VLVT_UINT64:
                VL_SNPRINTF(outStr, outStrSz+1, "%llu",
                            static_cast<unsigned long long>(*(reinterpret_cast<QData*>(vop->varDatap()))));
                return;
            default:
                strcpy(outStr, "-1");
                _VL_VPI_ERROR(__FILE__, __LINE__,
                              "%s: Unsupported format (%s) for %s, maximum limit is 64 bits",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
                return;
            }
        } else if (value_p->format == vpiHexStrVal) {
            value_p->value.str = outStr;
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int chars = (vop->varp()->packed().elements()+3)>>2;
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                int i;
                if (chars > outStrSz) {
                  // limit maximum size of output to size of buffer to prevent overrun.
                  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s"
                                  " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                                  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                                  vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, chars);
                  chars = outStrSz;
                }
                for (i=0; i<chars; ++i) {
                    char val = (datap[i>>1]>>((i&1)<<2))&15;
                    if (i==(chars-1)) {
                        // most signifcant char, mask off non existant bits when vector
                        // size is not a multiple of 4
                        unsigned int rem = vop->varp()->packed().elements() & 3;
                        if (rem) {
                            // generate bit mask & zero non existant bits
                            val &= (1<<rem)-1;
                        }
                    }
                    outStr[chars-i-1] = "0123456789abcdef"[static_cast<int>(val)];
                }
                outStr[i] = '\0';
                return;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return;
            }
        } else if (value_p->format == vpiStringVal) {
            value_p->value.str = outStr;
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int bytes = VL_BYTES_I(vop->varp()->packed().elements());
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                int i;
                if (bytes > outStrSz) {
                  // limit maximum size of output to size of buffer to prevent overrun.
                  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s"
                                  " as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
                                  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                                  vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, bytes);
                  bytes = outStrSz;
                }
                for (i=0; i<bytes; ++i) {
                    char val = datap[bytes-i-1];
                     // other simulators replace [leading?] zero chars with spaces, replicate here.
                    outStr[i] = val?val:' ';
                }
                outStr[i] = '\0';
                return;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return;
            }
        } else if (value_p->format == vpiIntVal) {
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
                value_p->value.integer = *(reinterpret_cast<CData*>(vop->varDatap()));
                return;
            case VLVT_UINT16:
                value_p->value.integer = *(reinterpret_cast<SData*>(vop->varDatap()));
                return;
            case VLVT_UINT32:
                value_p->value.integer = *(reinterpret_cast<IData*>(vop->varDatap()));
                return;
            case VLVT_WDATA:  // FALLTHRU
            case VLVT_UINT64:  // FALLTHRU
            default:
                value_p->value.integer = 0;
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return;
            }
        } else if (value_p->format == vpiSuppressVal) {
            return;
        }
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s",
                      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
        return;
    }
    else if (VerilatedVpioConst* vop = VerilatedVpioConst::castp(object)) {
        if (value_p->format == vpiIntVal) {
          value_p->value.integer = vop->num();
          return;
        }
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
        return;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format %s",
                  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format));
}

vpiHandle vpi_put_value(vpiHandle object, p_vpi_value value_p,
                        p_vpi_time time_p, PLI_INT32 flags) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_put_value %p %p\n", object, value_p););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    if (VL_UNLIKELY(!value_p)) {
      _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_put_value with NULL value pointer");
      return 0;
    }
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
        VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi:   vpi_put_value name=%s fmt=%d vali=%d\n",
                                     vop->fullname(), value_p->format, value_p->value.integer);
                        VL_DBG_MSGF("- vpi:   varp=%p  putatp=%p\n",
                                     vop->varp()->datap(), vop->varDatap()););
        if (VL_UNLIKELY(!vop->varp()->isPublicRW())) {
            _VL_VPI_WARNING(__FILE__, __LINE__,
                            "Ignoring vpi_put_value to signal marked read-only,"
                            " use public_flat_rw instead: ",
                            vop->fullname());
            return 0;
        }
        if (value_p->format == vpiVectorVal) {
            if (VL_UNLIKELY(!value_p->value.vector)) return NULL;
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
                *(reinterpret_cast<CData*>(vop->varDatap()))
                    = value_p->value.vector[0].aval & vop->mask();
                return object;
            case VLVT_UINT16:
                *(reinterpret_cast<SData*>(vop->varDatap()))
                    = value_p->value.vector[0].aval & vop->mask();
                return object;
            case VLVT_UINT32:
                *(reinterpret_cast<IData*>(vop->varDatap()))
                    = value_p->value.vector[0].aval & vop->mask();
                return object;
            case VLVT_WDATA: {
                int words = VL_WORDS_I(vop->varp()->packed().elements());
                WDataOutP datap = (reinterpret_cast<EData*>(vop->varDatap()));
                for (int i=0; i<words; ++i) {
                    datap[i] = value_p->value.vector[i].aval;
                    if (i==(words-1)) {
                        datap[i] &= vop->mask();
                    }
                }
                return object;
            }
            case VLVT_UINT64: {
                *(reinterpret_cast<QData*>(vop->varDatap())) = _VL_SET_QII(
                    value_p->value.vector[1].aval & vop->mask(),
                    value_p->value.vector[0].aval);
                return object;
            }
            default: {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return NULL;
            }
            }
        } else if (value_p->format == vpiBinStrVal) {
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int bits = vop->varp()->packed().elements();
                int len  = strlen(value_p->value.str);
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                for (int i=0; i<bits; ++i) {
                    char set = (i < len)?(value_p->value.str[len-i-1]=='1'):0;
                    // zero bits 7:1 of byte when assigning to bit 0, else
                    // or in 1 if bit set
                    if (i&7) {
                        datap[i>>3] |= set<<(i&7);
                    } else {
                        datap[i>>3]  = set;
                    }
                }
                return object;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return 0;
            }
        } else if (value_p->format == vpiOctStrVal) {
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int chars = (vop->varp()->packed().elements()+2)/3;
                int bytes = VL_BYTES_I(vop->varp()->packed().elements());
                int len  = strlen(value_p->value.str);
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                div_t idx;
                datap[0] = 0;  // reset zero'th byte
                for (int i=0; i<chars; ++i) {
                    union {
                        char  byte[2];
                        short half;
                    } val;
                    idx = div(i*3, 8);
                    if (i < len) {
                        // ignore illegal chars
                        char digit = value_p->value.str[len-i-1];
                        if (digit >= '0' && digit <= '7') {
                            val.half = digit-'0';
                        } else {
                            _VL_VPI_WARNING(__FILE__, __LINE__,
                                            "%s: Non octal character '%c' in '%s' as value %s for %s",
                                            VL_FUNC, digit, value_p->value.str,
                                            VerilatedVpiError::strFromVpiVal(value_p->format),
                                            vop->fullname());
                            val.half = 0;
                        }
                    } else {
                        val.half = 0;
                    }
                    // align octal character to position within vector, note that
                    // the three bits may straddle a byte bounday so two byte wide
                    // assignments are made to adjacent bytes - but not if the least
                    // signifcant byte of the aligned value is the most significant
                    // byte of the destination.
                    val.half <<= idx.rem;
                    datap[idx.quot] |= val.byte[0];  // or in value
                    if ((idx.quot+1) < bytes) {
                        datap[idx.quot+1] = val.byte[1];  // this also resets
                        // all bits to 0 prior to or'ing above
                    }
                }
                // mask off non existant bits in the most significant byte
                if (idx.quot == (bytes-1)) {
                    datap[idx.quot] &= vop->mask_byte(idx.quot);
                } else if (idx.quot+1 == (bytes-1)) {
                    datap[idx.quot+1] &= vop->mask_byte(idx.quot+1);
                }
                // zero off remaining top bytes
                for (int i=idx.quot+2; i<bytes; ++i) {
                    datap[i] = 0;
                }
                return object;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return 0;
            }
        } else if (value_p->format == vpiDecStrVal) {
            char remainder[16];
            unsigned long long val;
            int success = sscanf(value_p->value.str, "%30llu%15s", &val, remainder);
            if (success < 1) {
                _VL_VPI_ERROR(__FILE__, __LINE__,
                              "%s: Parsing failed for '%s' as value %s for %s",
                              VL_FUNC, value_p->value.str,
                              VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
                return 0;
            }
            if (success > 1) {
                _VL_VPI_WARNING(__FILE__, __LINE__,
                                "%s: Trailing garbage '%s' in '%s' as value %s for %s",
                                VL_FUNC, remainder, value_p->value.str,
                                VerilatedVpiError::strFromVpiVal(value_p->format),
                                vop->fullname());
            }
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
                *(reinterpret_cast<CData*>(vop->varDatap())) = val & vop->mask(); break;
            case VLVT_UINT16:
                *(reinterpret_cast<SData*>(vop->varDatap())) = val & vop->mask(); break;
            case VLVT_UINT32:
                *(reinterpret_cast<IData*>(vop->varDatap())) = val & vop->mask(); break;
            case VLVT_UINT64: *(reinterpret_cast<QData*>(vop->varDatap())) = val;
                (reinterpret_cast<IData*>(vop->varDatap()))[1] &= vop->mask(); break;
            case VLVT_WDATA:
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__,
                              "%s: Unsupported format (%s) for %s, maximum limit is 64 bits",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return 0;
            }
            return object;
        } else if (value_p->format == vpiHexStrVal) {
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int chars = (vop->varp()->packed().elements()+3)>>2;
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                char* val = value_p->value.str;
                // skip hex ident if one is detected at the start of the string
                if (val[0] == '0' && (val[1] == 'x' || val[1] == 'X')) {
                    val += 2;
                }
                int len = strlen(val);
                for (int i=0; i<chars; ++i) {
                    char hex;
                    // compute hex digit value
                    if (i < len) {
                        char digit = val[len-i-1];
                        if (digit >= '0' && digit <= '9') hex = digit - '0';
                        else if (digit >= 'a' && digit <= 'f') hex = digit - 'a' + 10;
                        else if (digit >= 'A' && digit <= 'F') hex = digit - 'A' + 10;
                        else {
                             _VL_VPI_WARNING(__FILE__, __LINE__,
                                             "%s: Non hex character '%c' in '%s' as value %s for %s",
                                             VL_FUNC, digit, value_p->value.str,
                                             VerilatedVpiError::strFromVpiVal(value_p->format),
                                             vop->fullname());
                            hex = 0;
                        }
                    } else {
                        hex = 0;
                    }
                    // assign hex digit value to destination
                    if (i&1) {
                        datap[i>>1] |= hex<<4;
                    } else {
                        datap[i>>1]  = hex;  // this also resets all
                        // bits to 0 prior to or'ing above of the msb
                    }
                }
                // apply bit mask to most significant byte
                datap[(chars-1)>>1] &= vop->mask_byte((chars-1)>>1);
                return object;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return 0;
            }
        } else if (value_p->format == vpiStringVal) {
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
            case VLVT_UINT16:
            case VLVT_UINT32:
            case VLVT_UINT64:
            case VLVT_WDATA: {
                int bytes = VL_BYTES_I(vop->varp()->packed().elements());
                int len   = strlen(value_p->value.str);
                CData* datap = (reinterpret_cast<CData*>(vop->varDatap()));
                for (int i=0; i<bytes; ++i) {
                    // prepend with 0 values before placing string the least signifcant bytes
                    datap[i] = (i < len)?value_p->value.str[len-i-1]:0;
                }
                return object;
            }
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
                              VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
                              vop->fullname());
                return 0;
            }
        } else if (value_p->format == vpiIntVal) {
            switch (vop->varp()->vltype()) {
            case VLVT_UINT8:
                *(reinterpret_cast<CData*>(vop->varDatap()))
                    = vop->mask() & value_p->value.integer;
                return object;
            case VLVT_UINT16:
                *(reinterpret_cast<SData*>(vop->varDatap()))
                    = vop->mask() & value_p->value.integer;
                return object;
            case VLVT_UINT32:
                *(reinterpret_cast<IData*>(vop->varDatap()))
                    = vop->mask() & value_p->value.integer;
                return object;
            case VLVT_WDATA:  // FALLTHRU
            case VLVT_UINT64:  // FALLTHRU
            default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s", VL_FUNC,
                              VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
                return 0;
            }
        }
        _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) as requested for %s",
                      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
        return NULL;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for ??",
                  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format));
    return NULL;
}

void vpi_get_value_array(vpiHandle object, p_vpi_arrayvalue arrayvalue_p,
                                       PLI_INT32 *index_p, PLI_UINT32 num) {
    _VL_VPI_UNIMP(); return;
}
void vpi_put_value_array(vpiHandle object, p_vpi_arrayvalue arrayvalue_p,
                                       PLI_INT32 *index_p, PLI_UINT32 num) {
    _VL_VPI_UNIMP(); return;
}


// time processing

void vpi_get_time(vpiHandle object, p_vpi_time time_p) {
    VerilatedVpiImp::assertOneCheck();
    // cppcheck-suppress nullPointer
    if (VL_UNLIKELY(!time_p)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_get_time with NULL value pointer");
        return;
    }
    if (time_p->type == vpiSimTime) {
        QData qtime = VL_TIME_Q();
        WData itime[2];
        VL_SET_WQ(itime, qtime);
        time_p->low = itime[0];
        time_p->high = itime[1];
        return;
    }
    _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported type (%d)",
                  VL_FUNC, time_p->type);
    return;
}

// I/O routines

PLI_UINT32 vpi_mcd_open(PLI_BYTE8 *filenamep) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    return VL_FOPEN_S(filenamep, "wb");
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    VL_FCLOSE_I(mcd); return 0;
}

PLI_BYTE8 *vpi_mcd_name(PLI_UINT32 mcd) {
    _VL_VPI_UNIMP(); return 0;
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8 *formatp, ...) {
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    va_list ap;
    va_start(ap, formatp);
    int chars = vpi_mcd_vprintf(mcd, formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_printf(PLI_BYTE8 *formatp, ...) {
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

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8 *format, va_list ap) {
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
    Verilated::flushCall();
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

PLI_INT32 vpi_compare_objects(vpiHandle object1, vpiHandle object2) {
    _VL_VPI_UNIMP(); return 0;
}
PLI_INT32 vpi_chk_error(p_vpi_error_info error_info_p) {
    // executing vpi_chk_error does not reset error
    // error_info_p can be NULL, so only return level in that case
    VerilatedVpiImp::assertOneCheck();
    p_vpi_error_info _error_info_p = VerilatedVpiImp::error_info()->getError();
    if (error_info_p && _error_info_p) {
      *error_info_p = *_error_info_p;
    }
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
    vlog_info_p->argv = (PLI_BYTE8**)Verilated::getCommandArgs()->argv;
    vlog_info_p->product = (PLI_BYTE8*)Verilated::productName();
    vlog_info_p->version = (PLI_BYTE8*)Verilated::productVersion();
    return 1;
}

// routines added with 1364-2001

PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8 *dataLoc, PLI_INT32 numOfBytes) {
    _VL_VPI_UNIMP(); return 0;
}
PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8 *dataLoc, PLI_INT32 numOfBytes) {
    _VL_VPI_UNIMP(); return 0;
}
void *vpi_get_userdata(vpiHandle obj) {
    _VL_VPI_UNIMP(); return 0;
}
PLI_INT32 vpi_put_userdata(vpiHandle obj, void *userdata) {
    _VL_VPI_UNIMP(); return 0;
}

PLI_INT32 vpi_control(PLI_INT32 operation, ...) {
    VL_DEBUG_IF_PLI(VL_DBG_MSGF("- vpi: vpi_control %d\n", operation););
    VerilatedVpiImp::assertOneCheck();
    _VL_VPI_ERROR_RESET();
    switch (operation) {
    case vpiFinish: {
        VL_FINISH_MT(__FILE__, __LINE__, "*VPI*");
        return 1;
    }
    case vpiStop: {
        VL_STOP_MT(__FILE__, __LINE__, "*VPI*");
        return 1;
    }
    }
    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, ignoring",
                    VL_FUNC, VerilatedVpiError::strFromVpiProp(operation));
    return 0;
}

vpiHandle vpi_handle_by_multi_index(vpiHandle obj, PLI_INT32 num_index, PLI_INT32 *index_array) {
    _VL_VPI_UNIMP(); return 0;
}
