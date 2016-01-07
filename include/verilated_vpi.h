// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2016 by Wilson Snyder. This program is free software; you can
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

#ifndef _VERILATED_VPI_H_
#define _VERILATED_VPI_H_ 1 ///< Header Guard

#include "verilated.h"
#include "verilated_syms.h"

#include <list>
#include <set>
#include <map>

//======================================================================
// From IEEE 1800-2009 annex K

#include "vltstd/vpi_user.h"

//======================================================================
// Internal constants

#define VL_DEBUG_IF_PLI VL_DEBUG_IF
#define VL_VPI_LINE_SIZE 8192

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
    explicit VerilatedVpioConst(vlsint32_t num) : m_num(num) {}
    virtual ~VerilatedVpioConst() {}
    static inline VerilatedVpioConst* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioConst*>((VerilatedVpio*)h); }
    virtual const vluint32_t type() { return vpiUndefined; }
    vlsint32_t num() const { return m_num; }
};

class VerilatedVpioRange : public VerilatedVpio {
    const VerilatedRange* m_range;
    vlsint32_t                  m_iteration;
public:
    explicit VerilatedVpioRange(const VerilatedRange* range) : m_range(range), m_iteration(0) {}
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
    explicit VerilatedVpioScope(const VerilatedScope* scopep)
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
    explicit VerilatedVpioVarIter(const VerilatedScope* scopep)
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
    static void selfTest();
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

//======================================================================

#endif // Guard
