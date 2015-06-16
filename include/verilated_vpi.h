// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2015 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: VPI implementation code
///
///	This file must be compiled and linked against all objects
///	created from Verilator or called by Verilator that use the VPI.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#ifndef CHPI_VERILATED_VPI_H
#define CHPI_VERILATED_VPI_H 1

#include "verilated.h"
#include "verilated_syms.h"

//======================================================================
// From IEEE 1800-2009 annex K

#include "vltstd/vpi_user.h"

//======================================================================
// Internal macros

#define _VL_VPI_INTERNAL    VerilatedVpi::error_info()->setMessage(vpiInternal)->setMessage
#define _VL_VPI_SYSTEM      VerilatedVpi::error_info()->setMessage(vpiSystem  )->setMessage
#define _VL_VPI_ERROR       VerilatedVpi::error_info()->setMessage(vpiError   )->setMessage
#define _VL_VPI_WARNING     VerilatedVpi::error_info()->setMessage(vpiWarning )->setMessage
#define _VL_VPI_NOTICE      VerilatedVpi::error_info()->setMessage(vpiNotice  )->setMessage
#define _VL_VPI_ERROR_RESET VerilatedVpi::error_info()->resetError

// Not supported yet
#define _VL_VPI_UNIMP() \
    _VL_VPI_ERROR(__FILE__,__LINE__,Verilated::catName("Unsupported VPI function: ",VL_FUNC));

//======================================================================
// Implementation

#include <set>
#include <list>
#include <map>

#define VL_DEBUG_IF_PLI VL_DEBUG_IF
#define VL_VPI_LINE_SIZE 8192

// Base VPI handled object
class VerilatedVpio {
    // MEM MANGLEMENT
    static vluint8_t* s_freeHead;

public:
    // CONSTRUCTORS
    VerilatedVpio() {}
    virtual ~VerilatedVpio() {}
    inline static void* operator new(size_t size) {
	// We new and delete tons of vpi structures, so keep them around
	// To simplify our free list, we use a size large enough for all derived types
	// We reserve word zero for the next pointer, as that's safer in case a
	// dangling reference to the original remains around.
	static size_t chunk = 96;
	if (VL_UNLIKELY(size>chunk)) vl_fatal(__FILE__,__LINE__,"", "increase chunk");
	if (VL_LIKELY(s_freeHead)) {
	    vluint8_t* newp = s_freeHead;
	    s_freeHead = *((vluint8_t**)newp);
	    return newp+8;
	} else {
	    // +8: 8 bytes for next
	    vluint8_t* newp = (vluint8_t*)(::operator new(chunk+8));
	    return newp+8;
	}
    }
    inline static void operator delete(void* obj, size_t size) {
	vluint8_t* oldp = ((vluint8_t*)obj)-8;
	*((void**)oldp) = s_freeHead;
	s_freeHead = oldp;
    }
    // MEMBERS
    static inline VerilatedVpio* castp(vpiHandle h) { return dynamic_cast<VerilatedVpio*>((VerilatedVpio*)h); }
    inline vpiHandle castVpiHandle() { return (vpiHandle)(this); }
    // ACCESSORS
    virtual const char* name() { return "<null>"; }
    virtual const char* fullname() { return "<null>"; }
    virtual const char* defname() { return "<null>"; }
    virtual const vluint32_t type() { return 0; }
    virtual const vluint32_t size() const { return 0; }
    virtual const VerilatedRange* rangep() const { return NULL; }
    virtual vpiHandle dovpi_scan() { return 0; }
};

typedef PLI_INT32 (*VerilatedPliCb)(struct t_cb_data *);

class VerilatedVpioCb : public VerilatedVpio {
    t_cb_data		m_cbData;
    s_vpi_value		m_value;
    QData		m_time;
public:
    // cppcheck-suppress uninitVar  // m_value
    VerilatedVpioCb(const t_cb_data* cbDatap, QData time)
	: m_cbData(*cbDatap), m_time(time) {
        m_value.format = cbDatap->value ? cbDatap->value->format : vpiSuppressVal;
	m_cbData.value = &m_value;
    }
    virtual ~VerilatedVpioCb() {}
    static inline VerilatedVpioCb* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioCb*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiCallback; }
    vluint32_t reason() const { return m_cbData.reason; }
    VerilatedPliCb cb_rtnp() const { return m_cbData.cb_rtn; }
    t_cb_data* cb_datap() { return &(m_cbData); }
    QData time() const { return m_time; }
};

class VerilatedVpioConst : public VerilatedVpio {
    vlsint32_t	m_num;
public:
    VerilatedVpioConst(vlsint32_t num) : m_num(num) {}
    virtual ~VerilatedVpioConst() {}
    static inline VerilatedVpioConst* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioConst*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiUndefined; }
    vlsint32_t num() const { return m_num; }
};

class VerilatedVpioRange : public VerilatedVpio {
    const VerilatedRange* m_range;
    vlsint32_t                  m_iteration;
public:
    VerilatedVpioRange(const VerilatedRange* range) : m_range(range), m_iteration(0) {}
    virtual ~VerilatedVpioRange() {}
    static inline VerilatedVpioRange* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioRange*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiRange; }
    virtual const vluint32_t size() const { return m_range->elements(); }
    virtual const VerilatedRange* rangep() const { return m_range; }
    int iteration() const { return m_iteration; }
    void iterationInc() { ++m_iteration; }
    virtual vpiHandle dovpi_scan() {
	if (!iteration()) {
	    VerilatedVpioRange* nextp = new VerilatedVpioRange(*this);
	    nextp->iterationInc();
	    return ((nextp)->castVpiHandle());
	} else {
	    return 0;  // End of list - only one deep
	}
    }
};

class VerilatedVpioScope : public VerilatedVpio {
    const VerilatedScope*	m_scopep;
public:
    VerilatedVpioScope(const VerilatedScope* scopep)
	: m_scopep(scopep) {}
    virtual ~VerilatedVpioScope() {}
    static inline VerilatedVpioScope* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioScope*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiScope; }
    const VerilatedScope* scopep() const { return m_scopep; }
    virtual const char* name() { return m_scopep->name(); }
    virtual const char* fullname() { return m_scopep->name(); }
};

class VerilatedVpioVar : public VerilatedVpio {
    const VerilatedVar*		m_varp;
    const VerilatedScope*	m_scopep;
    vluint8_t*			m_prevDatap;	// Previous value of data, for cbValueChange
    union {
	vluint8_t u8[4];
	vluint32_t u32;
    } m_mask;                                   // memoized variable mask
    vluint32_t			m_entSize;	// memoized variable size
protected:
    void*			m_varDatap;	// varp()->datap() adjusted for array entries
    vlsint32_t			m_index;
    const VerilatedRange&	get_range() const {
	// Determine number of dimensions and return outermost
	return (m_varp->dims()>1) ? m_varp->array() : m_varp->range();
    }
public:
    VerilatedVpioVar(const VerilatedVar* varp, const VerilatedScope* scopep)
	: m_varp(varp), m_scopep(scopep), m_index(0) {
	m_prevDatap = NULL;
	m_mask.u32 = VL_MASK_I(varp->range().elements());
	m_entSize = varp->entSize();
	m_varDatap = varp->datap();
    }
    virtual ~VerilatedVpioVar() {
	if (m_prevDatap) { delete [] m_prevDatap; m_prevDatap = NULL; }
    }
    static inline VerilatedVpioVar* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioVar*>((VerilatedVpio*)h); }
    const VerilatedVar* varp() const { return m_varp; }
    const VerilatedScope* scopep() const { return m_scopep; }
    vluint32_t mask() const { return m_mask.u32; }
    vluint8_t mask_byte(int idx) { return m_mask.u8[idx & 3]; }
    vluint32_t entSize() const { return m_entSize; }
    const vluint32_t index() { return m_index; }
    virtual const vluint32_t type() {
      if (varp()->vldir() != vpiNoDirection) return vpiPort;
      return (varp()->dims()>1) ? vpiMemory : vpiReg; /* but might be wire, logic */
    }
    virtual const vluint32_t size() const { return get_range().elements(); }
    virtual const VerilatedRange* rangep() const { return &get_range(); }
    virtual const char* name() { return m_varp->name(); }
    virtual const char* fullname() {
	VL_STATIC_OR_THREAD string out;
	out = string(m_scopep->name())+"."+name();
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
    static inline VerilatedVpioMemoryWord* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioMemoryWord*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiMemoryWord; }
    virtual const vluint32_t size() const { return varp()->range().elements(); }
    virtual const VerilatedRange* rangep() const { return &(varp()->range()); }
    virtual const char* fullname() {
	VL_STATIC_OR_THREAD string out;
	char num[20]; sprintf(num,"%d",m_index);
	out = string(scopep()->name())+"."+name()+"["+num+"]";
	return out.c_str();
    }
};

class VerilatedVpioVarIter : public VerilatedVpio {
    const VerilatedScope*	m_scopep;
    VerilatedVarNameMap::iterator m_it;
    bool m_started;
public:
    VerilatedVpioVarIter(const VerilatedScope* scopep)
	: m_scopep(scopep), m_started(false) {  }
    virtual ~VerilatedVpioVarIter() {}
    static inline VerilatedVpioVarIter* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioVarIter*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiIterator; }
    virtual vpiHandle dovpi_scan() {
	if (VL_LIKELY(m_scopep->varsp())) {
	    VerilatedVarNameMap* varsp = m_scopep->varsp();
	    if (VL_UNLIKELY(!m_started)) { m_it = varsp->begin(); m_started=true; }
	    else if (VL_UNLIKELY(m_it == varsp->end())) return 0;
	    else ++m_it;
	    if (m_it == varsp->end()) return 0;
	    return ((new VerilatedVpioVar(&(m_it->second), m_scopep))
		    ->castVpiHandle());
	} else {
	    return 0;  // End of list - only one deep
	}
    }
};

class VerilatedVpioMemoryWordIter : public VerilatedVpio {
    const vpiHandle		m_handle;
    const VerilatedVar*		m_varp;
    vlsint32_t                  m_iteration;
    vlsint32_t                  m_direction;
    bool                        m_done;
public:
    VerilatedVpioMemoryWordIter(const vpiHandle handle, const VerilatedVar* varp)
	: m_handle(handle), m_varp(varp), m_iteration(varp->array().right()), m_direction(VL_LIKELY(varp->array().left()>varp->array().right())?1:-1), m_done(false) {  }
    virtual ~VerilatedVpioMemoryWordIter() {}
    static inline VerilatedVpioMemoryWordIter* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioMemoryWordIter*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiIterator; }
    void iterationInc() { if (!(m_done = (m_iteration == m_varp->array().left()))) m_iteration+=m_direction; }
    virtual vpiHandle dovpi_scan() {
	vpiHandle result;
	if (m_done) return 0;
	result = vpi_handle_by_index(m_handle, m_iteration);
	iterationInc();
	return result;
    }
};

//======================================================================

struct VerilatedVpiTimedCbsCmp {
    /// Ordering sets keyed by time, then callback descriptor
    bool operator() (const pair<QData,VerilatedVpioCb*>& a,
		     const pair<QData,VerilatedVpioCb*>& b) const {
	if (a.first < b.first) return 1;
	if (a.first > b.first) return 0;
	return a.second < b.second;
    }
};

class VerilatedVpiError;

class VerilatedVpi {
    enum { CB_ENUM_MAX_VALUE = cbAtEndOfSimTime+1 };	// Maxium callback reason
    typedef list<VerilatedVpioCb*> VpioCbList;
    typedef set<pair<QData,VerilatedVpioCb*>,VerilatedVpiTimedCbsCmp > VpioTimedCbs;

    struct product_info {
	PLI_BYTE8* product;
	PLI_BYTE8* version;
    };

    VpioCbList		m_cbObjLists[CB_ENUM_MAX_VALUE];	// Callbacks for each supported reason
    VpioTimedCbs	m_timedCbs;	// Time based callbacks
    VerilatedVpiError*  m_errorInfop;	// Container for vpi error info

    static VerilatedVpi s_s;		// Singleton

public:
    VerilatedVpi() { m_errorInfop=NULL; }
    ~VerilatedVpi() {}
    static void cbReasonAdd(VerilatedVpioCb* vop) {
	if (vop->reason() == cbValueChange) {
	    if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
		varop->createPrevDatap();
	    }
	}
	if (VL_UNLIKELY(vop->reason() >= CB_ENUM_MAX_VALUE)) vl_fatal(__FILE__,__LINE__,"", "vpi bb reason too large");
	s_s.m_cbObjLists[vop->reason()].push_back(vop);
    }
    static void cbTimedAdd(VerilatedVpioCb* vop) {
	s_s.m_timedCbs.insert(make_pair(vop->time(), vop));
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
	VpioTimedCbs::iterator it=s_s.m_timedCbs.find(make_pair(cbp->time(),cbp));
	if (VL_LIKELY(it != s_s.m_timedCbs.end())) {
	    s_s.m_timedCbs.erase(it);
	}
    }
    static void callTimedCbs() {
	QData time = VL_TIME_Q();
	for (VpioTimedCbs::iterator it=s_s.m_timedCbs.begin(); it!=s_s.m_timedCbs.end(); ) {
	    if (VL_UNLIKELY(it->first <= time)) {
		VerilatedVpioCb* vop = it->second;
		++it;  // iterator may be deleted by callback
		VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  timed_callback %p\n",vop););
		(vop->cb_rtnp()) (vop->cb_datap());
	    }
	    else { ++it; }
	}
    }
    static QData cbNextDeadline() {
	VpioTimedCbs::iterator it=s_s.m_timedCbs.begin();
	if (VL_LIKELY(it!=s_s.m_timedCbs.end())) {
	    return it->first;
	} else {
	    return ~VL_ULL(0);  // maxquad
	}
    }
    static void callCbs(vluint32_t reason) {
	VpioCbList& cbObjList = s_s.m_cbObjLists[reason];
	for (VpioCbList::iterator it=cbObjList.begin(); it!=cbObjList.end();) {
	    if (VL_UNLIKELY(!*it)) { // Deleted earlier, cleanup
		it = cbObjList.erase(it);
		continue;
	    }
	    VerilatedVpioCb* vop = *it++;
	    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  reason_callback %d %p\n",reason,vop););
	    (vop->cb_rtnp()) (vop->cb_datap());
	}
    }
    static void callValueCbs() {
	VpioCbList& cbObjList = s_s.m_cbObjLists[cbValueChange];
        set<VerilatedVpioVar*> update; // set of objects to update after callbacks
	for (VpioCbList::iterator it=cbObjList.begin(); it!=cbObjList.end();) {
	    if (VL_UNLIKELY(!*it)) { // Deleted earlier, cleanup
		it = cbObjList.erase(it);
		continue;
	    }
	    VerilatedVpioCb* vop = *it++;
	    if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
		void* newDatap = varop->varDatap();
		void* prevDatap = varop->prevDatap();  // Was malloced when we added the callback
		VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  value_test %s v[0]=%d/%d %p %p\n",
					  varop->fullname(), *((CData*)newDatap), *((CData*)prevDatap),
					  newDatap, prevDatap););
		if (memcmp(prevDatap, newDatap, varop->entSize())) {
		    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  value_callback %p %s v[0]=%d\n",
					      vop,varop->fullname(), *((CData*)newDatap)););
                    update.insert(varop);
		    vpi_get_value(vop->cb_datap()->obj, vop->cb_datap()->value);
		    (vop->cb_rtnp()) (vop->cb_datap());
		}
	    }
	}
	for (set<VerilatedVpioVar*>::iterator it=update.begin(); it!=update.end(); ++it) {
	    memcpy((*it)->prevDatap(), (*it)->varDatap(), (*it)->entSize());
	}
    }

    static VerilatedVpiError* error_info(); // getter for vpi error info
};

#define _VL_VPI_ERROR_SET \
    do { \
        va_list args; \
        va_start(args, message); \
        VL_VSNPRINTF(m_buff, sizeof(m_buff), message.c_str(), args); \
        va_end(args); \
    } while (0)

class VerilatedVpiError {
    //// Container for vpi error info

    t_vpi_error_info m_errorInfo;
    bool             m_flag;
    char             m_buff[VL_VPI_LINE_SIZE];
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
        // We need to run above code first because in the case that the callback executes further vpi
        // functions we will loose the error as it will be overwritten.
	VerilatedVpi::callCbs(cbPLIError);
    }
public:

    VerilatedVpiError() : m_flag(false) {
	m_buff[0] = '\0';
	m_errorInfo.product = (PLI_BYTE8*)Verilated::productName();
    }
    ~VerilatedVpiError() {}
    VerilatedVpiError* setMessage(PLI_INT32 level) {
	m_flag=true;
	m_errorInfo.level = level;
        return this;
    }
    void setMessage(string file, PLI_INT32 line, string message, ...) {
	static VL_THREAD string filehold;
        _VL_VPI_ERROR_SET;
        m_errorInfo.state = vpiPLI;
	filehold = file;
        setError((PLI_BYTE8*)m_buff, NULL, (PLI_BYTE8*)filehold.c_str(), line);
    }
    p_vpi_error_info getError() {
	if (m_flag) return &m_errorInfo;
	return NULL;
    }
    void resetError() {
	m_flag=false;
    }
    static void vpi_unsupported() {
	// Not supported yet
	p_vpi_error_info error_info_p = VerilatedVpi::error_info()->getError();
	if (error_info_p) {
	    vl_fatal(error_info_p->file, error_info_p->line, "", error_info_p->message);
	    return;
	}
        vl_fatal(__FILE__, __LINE__, "", "vpi_unsupported called without error info set");
    }
    static const char* strFromVpiVal(PLI_INT32 vpiVal);
    static const char* strFromVpiObjType(PLI_INT32 vpiVal);
    static const char* strFromVpiMethod(PLI_INT32 vpiVal);
    static const char* strFromVpiCallbackReason(PLI_INT32 vpiVal);
    static const char* strFromVpiProp(PLI_INT32 vpiVal);
};

VerilatedVpiError* VerilatedVpi::error_info() {
    if (s_s.m_errorInfop == NULL) {
	s_s.m_errorInfop = new VerilatedVpiError();
    }
    return s_s.m_errorInfop;
}

// callback related

vpiHandle vpi_register_cb(p_cb_data cb_data_p) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!cb_data_p)) {
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s : callback data pointer is null", VL_FUNC);
        return NULL;
    }
    switch (cb_data_p->reason) {
    case cbAfterDelay: {
	QData time = 0;
	if (cb_data_p->time) time = _VL_SET_QII(cb_data_p->time->high, cb_data_p->time->low);
	VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, VL_TIME_Q()+time);
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_register_cb %d %p delay=%" VL_PRI64 "d\n",cb_data_p->reason,vop,time););
	VerilatedVpi::cbTimedAdd(vop);
	return vop->castVpiHandle();
    }
    case cbReadWriteSynch:		// FALLTHRU // Supported via vlt_main.cpp
    case cbReadOnlySynch:		// FALLTHRU // Supported via vlt_main.cpp
    case cbNextSimTime:			// FALLTHRU // Supported via vlt_main.cpp
    case cbStartOfSimulation:		// FALLTHRU // Supported via vlt_main.cpp
    case cbEndOfSimulation:		// FALLTHRU // Supported via vlt_main.cpp
    case cbValueChange:			// FALLTHRU // Supported via vlt_main.cpp
    case cbPLIError:			// FALLTHRU // NOP, but need to return handle, so make object
    case cbEnterInteractive:		// FALLTHRU // NOP, but need to return handle, so make object
    case cbExitInteractive:		// FALLTHRU // NOP, but need to return handle, so make object
    case cbInteractiveScopeChange: {	// FALLTHRU // NOP, but need to return handle, so make object
	VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, 0);
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_register_cb %d %p\n",cb_data_p->reason,vop););
	VerilatedVpi::cbReasonAdd(vop);
	return vop->castVpiHandle();
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported callback type %s",
			VL_FUNC, VerilatedVpiError::strFromVpiCallbackReason(cb_data_p->reason));
	return NULL;
    };
}

PLI_INT32 vpi_remove_cb(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_remove_cb %p\n",object););
    VerilatedVpioCb* vop = VerilatedVpioCb::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!vop)) return 0;
    if (vop->cb_datap()->reason == cbAfterDelay) {
	VerilatedVpi::cbTimedRemove(vop);
    } else {
	VerilatedVpi::cbReasonRemove(vop);
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
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!namep)) return NULL;
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle_by_name %s %p\n",namep,scope););
    VerilatedVpioScope* voScopep = VerilatedVpioScope::castp(scope);
    const VerilatedVar* varp;
    const VerilatedScope* scopep;
    string scopeAndName = namep;
    if (voScopep) {
	scopeAndName = string(voScopep->fullname()) + "." + namep;
	namep = (PLI_BYTE8*)scopeAndName.c_str();
    }
    {
	// This doesn't yet follow the hierarchy in the proper way
	scopep = Verilated::scopeFind(namep);
	if (scopep) {  // Whole thing found as a scope
	    return (new VerilatedVpioScope(scopep))->castVpiHandle();
	}
	const char* baseNamep = scopeAndName.c_str();
	string scopename;
	const char* dotp = strrchr(namep, '.');
	if (VL_LIKELY(dotp)) {
	    baseNamep = dotp+1;
	    scopename = string(namep,dotp-namep);
	}
	scopep = Verilated::scopeFind(scopename.c_str());
	if (!scopep) return NULL;
	varp = scopep->varFind(baseNamep);
    }
    if (!varp) return NULL;
    return (new VerilatedVpioVar(varp, scopep))->castVpiHandle();
}

vpiHandle vpi_handle_by_index(vpiHandle object, PLI_INT32 indx) {
    // Used to get array entries
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle_by_index %p %d\n",object, indx););
    VerilatedVpioVar* varop = VerilatedVpioVar::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_LIKELY(varop)) {
	if (varop->varp()->dims()<2) return 0;
	if (VL_LIKELY(varop->varp()->array().left() >= varop->varp()->array().right())) {
	    if (VL_UNLIKELY(indx > varop->varp()->array().left() || indx < varop->varp()->array().right())) return 0;
	    return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
					      indx - varop->varp()->array().right()))
		->castVpiHandle();
	} else {
	    if (VL_UNLIKELY(indx < varop->varp()->array().left() || indx > varop->varp()->array().right())) return 0;
	    return (new VerilatedVpioMemoryWord(varop->varp(), varop->scopep(), indx,
					      indx - varop->varp()->array().left()))
		->castVpiHandle();
	}
    } else {
	_VL_VPI_INTERNAL(__FILE__, __LINE__, "%s : can't resolve handle", VL_FUNC);
        return 0;
    }
}

// for traversing relationships

vpiHandle vpi_handle(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle %d %p\n",type,object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
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
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_iterate %d %p\n",type,object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (type) {
    case vpiMemoryWord: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (vop->varp()->dims() < 2) return 0;
	if (vop->varp()->dims() > 2) {
	    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: %s, object %s has unsupported number of indices (%d)",
			    VL_FUNC, VerilatedVpiError::strFromVpiMethod(type), vop->fullname() , vop->varp()->dims());
	}
	return (new VerilatedVpioMemoryWordIter(object, vop->varp()))->castVpiHandle();
    }
    case vpiRange: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (vop->varp()->dims() < 2) return 0;
	// Unsupported is multidim list
        if (vop->varp()->dims() > 2) {
	    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: %s, object %s has unsupported number of indices (%d)",
			    VL_FUNC, VerilatedVpiError::strFromVpiMethod(type), vop->fullname() , vop->varp()->dims());
	}
	return ((new VerilatedVpioRange(vop->rangep()))->castVpiHandle());
    }
    case vpiReg: {
	VerilatedVpioScope* vop = VerilatedVpioScope::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return ((new VerilatedVpioVarIter(vop->scopep()))
		->castVpiHandle());
    }
    default:
        _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Unsupported type %s, nothing will be returned",
			VL_FUNC, VerilatedVpiError::strFromVpiObjType(type));
	return 0;
    }
}
vpiHandle vpi_scan(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_scan %p\n",object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    if (VL_UNLIKELY(!vop)) return NULL;
    return vop->dovpi_scan();
}

// for processing properties

PLI_INT32 vpi_get(PLI_INT32 property, vpiHandle object) {
    // Leave this in the header file - in many cases the compiler can constant propagate "object"
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get %d %p\n",property,object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (property) {
    case vpiTimePrecision: {
	return VL_TIME_PRECISION;
    }
    case vpiType: {
	VerilatedVpio* vop = VerilatedVpioVar::castp(object);
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
        return (property==vpiVector)^(vop->varp()->dims()==0);
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
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get_str %d %p\n",property,object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
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
    static VL_THREAD char outStr[1+VL_MULS_MAX_WORDS*32]; // Maximum required size is for binary string, one byte per bit plus null termination
    // cppcheck-suppress variableScope
    static VL_THREAD int outStrSz = sizeof(outStr)-1;
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get_value %p\n",object););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!value_p)) return;
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	// We used to presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
        // This may cause backward compatability issues with older code.
	if (value_p->format == vpiVectorVal) {
	    // Vector pointer must come from our memory pool
	    // It only needs to persist until the next vpi_get_value
	    static VL_THREAD t_vpi_vecval out[VL_MULS_MAX_WORDS*2];
	    value_p->value.vector = out;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		out[0].aval = *((CData*)(vop->varDatap()));
		out[0].bval = 0;
		return;
	    case VLVT_UINT16:
		out[0].aval = *((SData*)(vop->varDatap()));
		out[0].bval = 0;
		return;
	    case VLVT_UINT32:
		out[0].aval = *((IData*)(vop->varDatap()));
		out[0].bval = 0;
		return;
	    case VLVT_WDATA: {
		int words = VL_WORDS_I(vop->varp()->range().elements());
		if (VL_UNLIKELY(words >= VL_MULS_MAX_WORDS)) {
		    vl_fatal(__FILE__,__LINE__,"", "vpi_get_value with more than VL_MULS_MAX_WORDS; increase and recompile");
		}
		WDataInP datap = ((IData*)(vop->varDatap()));
		for (int i=0; i<words; i++) {
		    out[i].aval = datap[i];
		    out[i].bval = 0;
		}
		return;
	    }
	    case VLVT_UINT64: {
		QData data = *((QData*)(vop->varDatap()));
		out[1].aval = (IData)(data>>VL_ULL(32));
		out[1].bval = 0;
		out[0].aval = (IData)(data);
		out[0].bval = 0;
		return;
	    }
	    default: {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	    }
	} else if (value_p->format == vpiBinStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bits = vop->varp()->range().elements();
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (bits > outStrSz) {
		  // limit maximum size of output to size of buffer to prevent overrun.
		  bits = outStrSz;
		  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, bits);
		}
		for (i=0; i<bits; i++) {
		    char val = (datap[i>>3]>>(i&7))&1;
		    outStr[bits-i-1] = val?'1':'0';
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiOctStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+2)/3;
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (chars > outStrSz) {
		    // limit maximum size of output to size of buffer to prevent overrun.
		    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				    VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, chars);
		    chars = outStrSz;
	        }
		for (i=0; i<chars; i++) {
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
			unsigned int rem = vop->varp()->range().elements() % 3;
                        if (rem) {
			    // generate bit mask & zero non existant bits
                            val &= (1<<rem)-1;
			}
		    }
		    outStr[chars-i-1] = '0' + (val&7);
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
                strcpy(outStr, "0");
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiDecStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    // outStrSz does not include NULL termination so add one
	    case VLVT_UINT8 : VL_SNPRINTF(outStr, outStrSz+1, "%hhu", (unsigned char )*((CData*)(vop->varDatap()))); return;
	    case VLVT_UINT16: VL_SNPRINTF(outStr, outStrSz+1, "%hu",  (unsigned short)*((SData*)(vop->varDatap()))); return;
	    case VLVT_UINT32: VL_SNPRINTF(outStr, outStrSz+1, "%u",   (unsigned int  )*((IData*)(vop->varDatap()))); return;
	    case VLVT_UINT64: VL_SNPRINTF(outStr, outStrSz+1, "%llu",  (unsigned long long)*((QData*)(vop->varDatap()))); return;
	    default:
                strcpy(outStr, "-1");
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s, maximum limit is 64 bits",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiHexStrVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+3)>>2;
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (chars > outStrSz) {
		  // limit maximum size of output to size of buffer to prevent overrun.
		  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, chars);
		  chars = outStrSz;
		}
		for (i=0; i<chars; i++) {
		    char val = (datap[i>>1]>>((i&1)<<2))&15;
                    static char hex[] = "0123456789abcdef";
                    if (i==(chars-1)) {
			// most signifcant char, mask off non existant bits when vector
                        // size is not a multiple of 4
			unsigned int rem = vop->varp()->range().elements() & 3;
                        if (rem) {
			    // generate bit mask & zero non existant bits
                            val &= (1<<rem)-1;
			}
		    }
		    outStr[chars-i-1] = hex[static_cast<int>(val)];
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiStringVal) {
	    value_p->value.str = outStr;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		CData* datap = ((CData*)(vop->varDatap()));
		int i;
		if (bytes > outStrSz) {
		  // limit maximum size of output to size of buffer to prevent overrun.
		  _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Truncating string value of %s for %s as buffer size (%d, VL_MULS_MAX_WORDS=%d) is less than required (%d)",
				  VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format),
				  vop->fullname(), outStrSz, VL_MULS_MAX_WORDS, bytes);
		  bytes = outStrSz;
		}
		for (i=0; i<bytes; i++) {
		    char val = datap[bytes-i-1];
                     // other simulators replace [leading?] zero chars with spaces, replicate here.
		    outStr[i] = val?val:' ';
		}
		outStr[i]=0; // NULL terminate
		return;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return;
	    }
	} else if (value_p->format == vpiIntVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		value_p->value.integer = *((CData*)(vop->varDatap()));
		return;
	    case VLVT_UINT16:
		value_p->value.integer = *((SData*)(vop->varDatap()));
		return;
	    case VLVT_UINT32:
		value_p->value.integer = *((IData*)(vop->varDatap()));
		return;
	    case VLVT_WDATA:
	    case VLVT_UINT64:
		// Not legal
		value_p->value.integer = 0;
	    default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
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
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_put_value %p %p\n",object, value_p););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!value_p)) {
      _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_put_value with NULL value pointer");
      return 0;
    }
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:    vpi_put_value name=%s fmt=%d vali=%d\n",
				  vop->fullname(), value_p->format, value_p->value.integer);
			VL_PRINTF("-vltVpi:    varp=%p  putatp=%p\n",
				  vop->varp()->datap(), vop->varDatap()););
	if (VL_UNLIKELY(!vop->varp()->isPublicRW())) {
            _VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_put_value to signal marked read-only, use public_flat_rw instead: ", vop->fullname());
	    return 0;
	}
	if (value_p->format == vpiVectorVal) {
	    if (VL_UNLIKELY(!value_p->value.vector)) return NULL;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		*((CData*)(vop->varDatap())) = value_p->value.vector[0].aval & vop->mask();
		return object;
	    case VLVT_UINT16:
		*((SData*)(vop->varDatap())) = value_p->value.vector[0].aval & vop->mask();
		return object;
	    case VLVT_UINT32:
		*((IData*)(vop->varDatap())) = value_p->value.vector[0].aval & vop->mask();
		return object;
	    case VLVT_WDATA: {
		int words = VL_WORDS_I(vop->varp()->range().elements());
		WDataOutP datap = ((IData*)(vop->varDatap()));
		for (int i=0; i<words; i++) {
		    datap[i] = value_p->value.vector[i].aval;
                    if (i==(words-1)) {
			datap[i] &= vop->mask();
		    }
		}
		return object;
	    }
	    case VLVT_UINT64: {
		*((QData*)(vop->varDatap())) = _VL_SET_QII(
		    value_p->value.vector[1].aval & vop->mask(),
		    value_p->value.vector[0].aval);
		return object;
	    }
	    default: {
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return NULL;
	    }
	    }
	} else if (value_p->format == vpiBinStrVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bits = vop->varp()->range().elements();
		int len	 = strlen(value_p->value.str);
		CData* datap = ((CData*)(vop->varDatap()));
		for (int i=0; i<bits; i++) {
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
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiOctStrVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+2)/3;
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		int len	 = strlen(value_p->value.str);
		CData* datap = ((CData*)(vop->varDatap()));
                div_t idx;
                datap[0] = 0; // reset zero'th byte
		for (int i=0; i<chars; i++) {
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
			    _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Non octal character '%c' in '%s' as value %s for %s",
					    VL_FUNC, digit, value_p->value.str,
					    VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
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
                    datap[idx.quot] |= val.byte[0]; // or in value
                    if ((idx.quot+1) < bytes) {
		        datap[idx.quot+1] = val.byte[1]; // this also resets all bits to 0 prior to or'ing above
		    }
		}
                // mask off non existant bits in the most significant byte
                if (idx.quot == (bytes-1)) {
                    datap[idx.quot] &= vop->mask_byte(idx.quot);
		} else if (idx.quot+1 == (bytes-1)) {
                    datap[idx.quot+1] &= vop->mask_byte(idx.quot+1);
		}
                // zero off remaining top bytes
                for (int i=idx.quot+2; i<bytes; i++) {
		    datap[i] = 0;
		}
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiDecStrVal) {
            char remainder[16];
            unsigned long long val;
            int success = sscanf(value_p->value.str, "%30llu%15s", &val, remainder);
            if (success < 1) {
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Parsing failed for '%s' as value %s for %s",
			      VL_FUNC, value_p->value.str, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
                return 0;
	    }
            if (success > 1) {
		_VL_VPI_WARNING(__FILE__, __LINE__, "%s: Trailing garbage '%s' in '%s' as value %s for %s",
				VL_FUNC, remainder, value_p->value.str, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
	    }
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 : *((CData*)(vop->varDatap())) = val & vop->mask(); break;
	    case VLVT_UINT16: *((SData*)(vop->varDatap())) = val & vop->mask(); break;
	    case VLVT_UINT32: *((IData*)(vop->varDatap())) = val & vop->mask(); break;
	    case VLVT_UINT64: *((QData*)(vop->varDatap())) = val; ((IData*)(vop->varDatap()))[1] &= vop->mask(); break;
	    case VLVT_WDATA:
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s, maximum limit is 64 bits",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
            return object;
	} else if (value_p->format == vpiHexStrVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int chars = (vop->varp()->range().elements()+3)>>2;
		CData* datap = ((CData*)(vop->varDatap()));
                char* val = value_p->value.str;
                // skip hex ident if one is detected at the start of the string
                if (val[0] == '0' && (val[1] == 'x' || val[1] == 'X')) {
		    val += 2;
		}
		int len = strlen(val);
		for (int i=0; i<chars; i++) {
                    char hex;
                    // compute hex digit value
                    if (i < len) {
                        char digit = val[len-i-1];
                        if (digit >= '0' && digit <= '9') hex = digit - '0';
                        else if (digit >= 'a' && digit <= 'f') hex = digit - 'a' + 10;
                        else if (digit >= 'A' && digit <= 'F') hex = digit - 'A' + 10;
                        else {
			     _VL_VPI_WARNING(__FILE__, __LINE__, "%s: Non hex character '%c' in '%s' as value %s for %s",
					     VL_FUNC, digit, value_p->value.str, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
			    hex = 0;
			}
		    } else {
			hex = 0;
		    }
                    // assign hex digit value to destination
		    if (i&1) {
		        datap[i>>1] |= hex<<4;
		    } else {
		        datap[i>>1]  = hex; // this also resets all bits to 0 prior to or'ing above of the msb
		    }
		}
                // apply bit mask to most significant byte
                datap[(chars-1)>>1] &= vop->mask_byte((chars-1)>>1);
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiStringVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8 :
	    case VLVT_UINT16:
	    case VLVT_UINT32:
	    case VLVT_UINT64:
	    case VLVT_WDATA: {
		int bytes = VL_BYTES_I(vop->varp()->range().elements());
		int len	  = strlen(value_p->value.str);
		CData* datap = ((CData*)(vop->varDatap()));
		for (int i=0; i<bytes; i++) {
		    datap[i] = (i < len)?value_p->value.str[len-i-1]:0; // prepend with 0 values before placing string the least signifcant bytes
		}
		return object;
	    }
	    default:
		_VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
		return 0;
	    }
	} else if (value_p->format == vpiIntVal) {
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		*((CData*)(vop->varDatap())) = vop->mask() & value_p->value.integer;
		return object;
	    case VLVT_UINT16:
		*((SData*)(vop->varDatap())) = vop->mask() & value_p->value.integer;
		return object;
	    case VLVT_UINT32:
		*((IData*)(vop->varDatap())) = vop->mask() & value_p->value.integer;
		return object;
	    case VLVT_WDATA: // FALLTHRU
	    case VLVT_UINT64: // FALLTHRU
	    default:
                _VL_VPI_ERROR(__FILE__, __LINE__, "%s: Unsupported format (%s) for %s",
			      VL_FUNC, VerilatedVpiError::strFromVpiVal(value_p->format), vop->fullname());
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
    if (VL_UNLIKELY(!time_p)) {
	_VL_VPI_WARNING(__FILE__, __LINE__, "Ignoring vpi_get_time with NULL value pointer");
	return;
    }
    if (time_p->type == vpiSimTime) {
	QData qtime = VL_TIME_Q();
	IData itime[2];
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
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    return VL_FOPEN_S(filenamep,"wb");
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    VL_FCLOSE_I(mcd); return 0;
}

PLI_BYTE8 *vpi_mcd_name(PLI_UINT32 mcd) {
    _VL_VPI_UNIMP(); return 0;
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8 *formatp, ...) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    va_list ap;
    va_start(ap,formatp);
    int chars = vpi_mcd_vprintf(mcd, formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_printf(PLI_BYTE8 *formatp, ...) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    va_list ap;
    va_start(ap,formatp);
    int chars = vpi_vprintf(formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* formatp, va_list ap) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    return VL_VPRINTF(formatp, ap);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8 *format, va_list ap) {
    FILE* fp = VL_CVT_I_FP(mcd);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!fp)) return 0;
    int chars = vfprintf(fp, format, ap);
    return chars;
}

PLI_INT32 vpi_flush(void) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    Verilated::flushCall();
    return 0;
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
    FILE* fp = VL_CVT_I_FP(mcd);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
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
    p_vpi_error_info _error_info_p = VerilatedVpi::error_info()->getError();
    if (error_info_p && _error_info_p) {
      *error_info_p = *_error_info_p;
    }
    if (!_error_info_p) return 0; // no error occured
    return _error_info_p->level;  // return error severity level
};

PLI_INT32 vpi_free_object(vpiHandle object) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    return vpi_release_handle(object);  // Deprecated
}

PLI_INT32 vpi_release_handle (vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_release_handle %p\n",object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    if (VL_UNLIKELY(!vop)) return 0;
    vpi_remove_cb(object);  // May not be a callback, but that's ok
    delete vop;
    return 1;
}

PLI_INT32 vpi_get_vlog_info(p_vpi_vlog_info vlog_info_p) {
    _VL_VPI_ERROR_RESET(); // reset vpi error status
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
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_control %d\n",operation););
    _VL_VPI_ERROR_RESET(); // reset vpi error status
    switch (operation) {
    case vpiFinish: {
	vl_finish(__FILE__,__LINE__,"*VPI*");
	return 1;
    }
    case vpiStop: {
	vl_stop(__FILE__,__LINE__,"*VPI*");
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

//======================================================================

#endif // Guard
