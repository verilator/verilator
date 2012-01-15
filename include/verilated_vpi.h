// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2012 by Wilson Snyder. This program is free software; you can
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
///	"//-" indicates features that are as yet unimplemented.
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

// Not supported yet
#define _VL_VPI_UNIMP() \
    vl_fatal(__FILE__,__LINE__,"",Verilated::catName("Unsupported VPI function: ",VL_FUNC))

//======================================================================
// Implementation

#include <set>

#define VL_DEBUG_IF_PLI VL_DEBUG_IF

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
	m_cbData.value = &m_value;
    }
    virtual ~VerilatedVpioCb() {}
    static inline VerilatedVpioCb* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioCb*>((VerilatedVpio*)h); }
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
    vlsint32_t num() const { return m_num; }
};

class VerilatedVpioRange : public VerilatedVpio {
    vlsint32_t	m_lhs;	// Ranges can be signed
    vlsint32_t	m_rhs;
    bool	m_iteration;
public:
    VerilatedVpioRange(vlsint32_t lhs, vlsint32_t rhs) : m_lhs(lhs), m_rhs(rhs), m_iteration(0) {}
    virtual ~VerilatedVpioRange() {}
    static inline VerilatedVpioRange* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioRange*>((VerilatedVpio*)h); }
    vlsint32_t lhs() const { return m_lhs; }
    vlsint32_t rhs() const { return m_rhs; }
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
    const VerilatedScope* scopep() const { return m_scopep; }
    virtual const char* name() { return m_scopep->name(); }
    virtual const char* fullname() { return m_scopep->name(); }
};

class VerilatedVpioVar : public VerilatedVpio {
    const VerilatedVar*		m_varp;
    const VerilatedScope*	m_scopep;
    vluint8_t*			m_prevDatap;	// Previous value of data, for cbValueChange
    vluint32_t			m_mask;		// memoized variable mask
    vluint32_t			m_entSize;	// memoized variable size
protected:
    void*			m_varDatap;	// varp()->datap() adjusted for array entries
    vlsint32_t			m_index;
public:
    VerilatedVpioVar(const VerilatedVar* varp, const VerilatedScope* scopep)
	: m_varp(varp), m_scopep(scopep), m_index(0) {
	m_prevDatap = NULL;
	m_mask = VL_MASK_I(varp->range().bits());
	m_entSize = varp->entSize();
	m_varDatap = varp->datap();
    }
    virtual ~VerilatedVpioVar() {
	if (m_prevDatap) { delete [] m_prevDatap; m_prevDatap = NULL; }
    }
    static inline VerilatedVpioVar* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioVar*>((VerilatedVpio*)h); }
    const VerilatedVar* varp() const { return m_varp; }
    const VerilatedScope* scopep() const { return m_scopep; }
    vluint32_t mask() const { return m_mask; }
    vluint32_t entSize() const { return m_entSize; }
    virtual const char* name() { return m_varp->name(); }
    virtual const char* fullname() {
	static VL_THREAD string out;
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

class VerilatedVpioVarIndex : public VerilatedVpioVar {
public:
    VerilatedVpioVarIndex(const VerilatedVar* varp, const VerilatedScope* scopep,
			  vlsint32_t index, int offset)
	: VerilatedVpioVar(varp, scopep) {
	m_index = index;
	m_varDatap = ((vluint8_t*)varp->datap()) + entSize()*offset;
    }
    virtual ~VerilatedVpioVarIndex() {}
    static inline VerilatedVpioVarIndex* castp(vpiHandle h) { return dynamic_cast<VerilatedVpioVarIndex*>((VerilatedVpio*)h); }
    virtual const char* fullname() {
	static VL_THREAD string out;
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
    virtual vpiHandle dovpi_scan() {
	if (VL_LIKELY(m_scopep->varsp())) {
	    if (VL_UNLIKELY(!m_started)) { m_it = m_scopep->varsp()->begin(); m_started=true; }
	    else if (VL_UNLIKELY(m_it == m_scopep->varsp()->end())) return 0;
	    else ++m_it;
	    if (m_it == m_scopep->varsp()->end()) return 0;
	    return ((new VerilatedVpioVar(&(m_it->second), m_scopep))
		    ->castVpiHandle());
	} else {
	    return 0;  // End of list - only one deep
	}
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

class VerilatedVpi {
    enum { CB_ENUM_MAX_VALUE = cbAtEndOfSimTime+1 };	// Maxium callback reason
    typedef set<VerilatedVpioCb*> VpioCbSet;
    typedef set<pair<QData,VerilatedVpioCb*>,VerilatedVpiTimedCbsCmp > VpioTimedCbs;

    VpioCbSet		m_cbObjSets[CB_ENUM_MAX_VALUE];	// Callbacks for each supported reason
    VpioTimedCbs	m_timedCbs;	// Time based callbacks

    static VerilatedVpi s_s;		// Singleton

public:
    VerilatedVpi() {}
    ~VerilatedVpi() {}
    static void cbReasonAdd(VerilatedVpioCb* vop) {
	if (vop->reason() == cbValueChange) {
	    if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
		varop->createPrevDatap();
	    }
	}
	if (VL_UNLIKELY(vop->reason() >= CB_ENUM_MAX_VALUE)) vl_fatal(__FILE__,__LINE__,"", "vpi bb reason too large");
	s_s.m_cbObjSets[vop->reason()].insert(vop);
    }
    static void cbTimedAdd(VerilatedVpioCb* vop) {
	s_s.m_timedCbs.insert(make_pair(vop->time(), vop));
    }
    static void cbReasonRemove(VerilatedVpioCb* cbp) {
	VpioCbSet& cbObjSet = s_s.m_cbObjSets[cbp->reason()];
	VpioCbSet::iterator it=cbObjSet.find(cbp);
	if (VL_LIKELY(it != cbObjSet.end())) {
	    cbObjSet.erase(it);
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
	VpioCbSet& cbObjSet = s_s.m_cbObjSets[reason];
	for (VpioCbSet::iterator it=cbObjSet.begin(); it!=cbObjSet.end();) {
	    VerilatedVpioCb* vop = *it;
	    ++it;  // iterator may be deleted by callback
	    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  reason_callback %d %p\n",reason,vop););
	    (vop->cb_rtnp()) (vop->cb_datap());
	}
    }
    static void callValueCbs() {
	VpioCbSet& cbObjSet = s_s.m_cbObjSets[cbValueChange];
	for (VpioCbSet::iterator it=cbObjSet.begin(); it!=cbObjSet.end();) {
	    VerilatedVpioCb* vop = *it;
	    ++it;  // iterator may be deleted by callback
	    if (VerilatedVpioVar* varop = VerilatedVpioVar::castp(vop->cb_datap()->obj)) {
		void* newDatap = varop->varDatap();
		void* prevDatap = varop->prevDatap();  // Was malloced when we added the callback
		VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  value_test %s v[0]=%d/%d %p %p\n",
					  varop->fullname(), *((CData*)newDatap), *((CData*)prevDatap),
					  newDatap, prevDatap););
		if (memcmp(prevDatap, newDatap, varop->entSize())) {
		    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  value_callback %p %s v[0]=%d\n",
					      vop,varop->fullname(), *((CData*)newDatap)););
		    memcpy(prevDatap, newDatap, varop->entSize());
		    vpi_get_value(vop->cb_datap()->obj, vop->cb_datap()->value);
		    (vop->cb_rtnp()) (vop->cb_datap());
		}
	    }
	}
    }
};

// callback related

vpiHandle vpi_register_cb(p_cb_data cb_data_p) {
    if (VL_UNLIKELY(!cb_data_p)) return NULL;
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
    case cbEnterInteractive:		// FALLTHRU // NOP, but need to return handle, so make object
    case cbExitInteractive:		// FALLTHRU // NOP, but need to return handle, so make object
    case cbInteractiveScopeChange: {	// FALLTHRU // NOP, but need to return handle, so make object
	VerilatedVpioCb* vop = new VerilatedVpioCb(cb_data_p, 0);
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_register_cb %d %p\n",cb_data_p->reason,vop););
	VerilatedVpi::cbReasonAdd(vop);
	return vop->castVpiHandle();
    }
    default:
	_VL_VPI_UNIMP(); return NULL;
    };
}

PLI_INT32 vpi_remove_cb(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_remove_cb %p\n",object););
    VerilatedVpioCb* vop = VerilatedVpioCb::castp(object);
    if (VL_UNLIKELY(!vop)) return 0;
    if (vop->cb_datap()->reason == cbAfterDelay) {
	VerilatedVpi::cbTimedRemove(vop);
    } else {
	VerilatedVpi::cbReasonRemove(vop);
    }
    return 1;
}

//-void vpi_get_cb_info(vpiHandle object, p_cb_data cb_data_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-vpiHandle vpi_register_systf(p_vpi_systf_data systf_data_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-void vpi_get_systf_info(vpiHandle object, p_vpi_systf_data systf_data_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

// for obtaining handles

vpiHandle vpi_handle_by_name(PLI_BYTE8* namep, vpiHandle scope) {
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
    if (VL_LIKELY(varop)) {
	if (varop->varp()->dims()<2) return 0;
	if (VL_LIKELY(varop->varp()->array().lhs() >= varop->varp()->array().rhs())) {
	    if (VL_UNLIKELY(indx > varop->varp()->array().lhs() || indx < varop->varp()->array().rhs())) return 0;
	    return (new VerilatedVpioVarIndex(varop->varp(), varop->scopep(), indx,
					      indx - varop->varp()->array().rhs()))
		->castVpiHandle();
	} else {
	    if (VL_UNLIKELY(indx < varop->varp()->array().lhs() || indx > varop->varp()->array().rhs())) return 0;
	    return (new VerilatedVpioVarIndex(varop->varp(), varop->scopep(), indx,
					      indx - varop->varp()->array().lhs()))
		->castVpiHandle();
	}
    } else {
	_VL_VPI_UNIMP(); return 0;
    }
}

// for traversing relationships

vpiHandle vpi_handle(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_handle %d %p\n",type,object););
    switch (type) {
    case vpiLeftRange:  // FALLTHRU
    case vpiRightRange: {
	if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	    vluint32_t num = ((type==vpiLeftRange)
			      ? vop->varp()->range().lhs()
			      : vop->varp()->range().rhs());
	    return (new VerilatedVpioConst(num))->castVpiHandle();
	} else if (VerilatedVpioRange* vop = VerilatedVpioRange::castp(object)) {
	    vluint32_t num = ((type==vpiLeftRange)
			      ? vop->lhs()
			      : vop->rhs());
	    return (new VerilatedVpioConst(num))->castVpiHandle();
	} else {
	    return 0;
	}
    }
    default:
	_VL_VPI_UNIMP();
	return 0;
    }
}

//-vpiHandle vpi_handle_multi(PLI_INT32 type, vpiHandle refHandle1, vpiHandle refHandle2, ... ) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

vpiHandle vpi_iterate(PLI_INT32 type, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_iterate %d %p\n",type,object););
    switch (type) {
    case vpiMemoryWord: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (vop->varp()->dims() < 2) return 0;
	// Unsupported is multidim list
	return ((new VerilatedVpioRange(vop->varp()->array().lhs(),
					vop->varp()->array().rhs()))
		->castVpiHandle());
    }
    case vpiReg: {
	VerilatedVpioScope* vop = VerilatedVpioScope::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return ((new VerilatedVpioVarIter(vop->scopep()))
		->castVpiHandle());
    }
    case vpiIODecl: // Skipping - we'll put under reg
    case vpiNet: // Skipping - we'll put under reg
	return 0;
    default:
	_VL_VPI_UNIMP(); return 0;
    }
}
vpiHandle vpi_scan(vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_scan %p\n",object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    if (VL_UNLIKELY(!vop)) return NULL;
    return vop->dovpi_scan();
}

// for processing properties

PLI_INT32 vpi_get(PLI_INT32 property, vpiHandle object) {
    // Leave this in the header file - in many cases the compiler can constant propagate "object"
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get %d %p\n",property,object););
    switch (property) {
    case vpiTimePrecision: {
	return VL_TIME_PRECISION;
    }
    case vpiType: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return ((vop->varp()->dims()>1) ? vpiMemory : vpiReg);
    }
    case vpiDirection: {
	// By forthought, the directions already are vpi enumerated
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	return vop->varp()->vldir();
    }
    case vpiVector: {
	VerilatedVpioVar* vop = VerilatedVpioVar::castp(object);
	if (VL_UNLIKELY(!vop)) return 0;
	if (vop->varp()->dims()==0) return 0;
	else return 1;
    }
    default:
	_VL_VPI_UNIMP();
	return 0;
    }
}

//-PLI_INT64 vpi_get64(PLI_INT32 property, vpiHandle object) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

PLI_BYTE8 *vpi_get_str(PLI_INT32 property, vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get_str %d %p\n",property,object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
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
	_VL_VPI_UNIMP();
	return 0;
    }
}

// delay processing

//-void vpi_get_delays(vpiHandle object, p_vpi_delay delay_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-void vpi_put_delays(vpiHandle object, p_vpi_delay delay_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

// value processing

void vpi_get_value(vpiHandle object, p_vpi_value value_p) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_get_value %p\n",object););
    if (VL_UNLIKELY(!value_p)) return;
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	// We presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
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
		int words = VL_WORDS_I(vop->varp()->range().bits());
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
		_VL_VPI_UNIMP();
		return;
	    }
	    }
	} else {
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
		_VL_VPI_UNIMP();
		return;
	    }
	}
    }
    else if (VerilatedVpioConst* vop = VerilatedVpioConst::castp(object)) {
	value_p->value.integer = vop->num();
	return;
    }
    _VL_VPI_UNIMP();
}

vpiHandle vpi_put_value(vpiHandle object, p_vpi_value value_p,
			p_vpi_time time_p, PLI_INT32 flags) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_put_value %p %p\n",object, value_p););
    if (VL_UNLIKELY(!value_p)) return 0;
    if (VerilatedVpioVar* vop = VerilatedVpioVar::castp(object)) {
	// We presume vpiValue.format = vpiIntVal or if single bit vpiScalarVal
	VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:    vpi_put_value name=%s fmt=%d vali=%d\n",
				  vop->fullname(), value_p->format, value_p->value.integer);
			VL_PRINTF("-vltVpi:    varp=%p  putatp=%p\n",
				  vop->varp()->datap(), vop->varDatap()););
	if (VL_UNLIKELY(!vop->varp()->isPublicRW())) {
	    VL_PRINTF("%%Warning: Ignoring vpi_put_value to signal marked read-only, use public_flat_rw instead: %s\n",
		      vop->fullname());
	    return 0;
	}
	if (value_p->format == vpiVectorVal) {
	    if (VL_UNLIKELY(!value_p->value.vector)) return NULL;
	    switch (vop->varp()->vltype()) {
	    case VLVT_UINT8:
		*((CData*)(vop->varDatap())) = value_p->value.vector[0].aval;
		return object;
	    case VLVT_UINT16:
		*((SData*)(vop->varDatap())) = value_p->value.vector[0].aval;
		return object;
	    case VLVT_UINT32:
		*((IData*)(vop->varDatap())) = value_p->value.vector[0].aval;
		return object;
	    case VLVT_WDATA: {
		int words = VL_WORDS_I(vop->varp()->range().bits());
		WDataOutP datap = ((IData*)(vop->varDatap()));
		for (int i=0; i<words; i++) {
		    datap[i] = value_p->value.vector[i].aval;
		}
		return object;
	    }
	    case VLVT_UINT64: {
		*((QData*)(vop->varDatap())) = _VL_SET_QII(
		    value_p->value.vector[1].aval,
		    value_p->value.vector[0].aval);
		return object;
	    }
	    default: {
		_VL_VPI_UNIMP();
		return NULL;
	    }
	    }
	} else {
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
		_VL_VPI_UNIMP();
		return 0;
	    }
	}
    }
    _VL_VPI_UNIMP(); return NULL;
}

//-void vpi_get_value_array(vpiHandle object, p_vpi_arrayvalue arrayvalue_p,
//-			 PLI_INT32 *index_p, PLI_UINT32 num) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-void vpi_put_value_array(vpiHandle object, p_vpi_arrayvalue arrayvalue_p,
//-			 PLI_INT32 *index_p, PLI_UINT32 num) {
//-    _VL_VPI_UNIMP(); return 0;
//-}


// time processing

//-void vpi_get_time(vpiHandle object, p_vpi_time time_p) {
//-    _VL_VPI_UNIMP();
//-}

// I/O routines

PLI_UINT32 vpi_mcd_open(PLI_BYTE8 *filenamep) {
    return VL_FOPEN_S(filenamep,"wb");
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
    VL_FCLOSE_I(mcd); return 0;
}

//-PLI_BYTE8 *vpi_mcd_name(PLI_UINT32 mcd) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8 *formatp, ...) {
    va_list ap;
    va_start(ap,formatp);
    int chars = vpi_mcd_vprintf(mcd, formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_printf(PLI_BYTE8 *formatp, ...) {
    va_list ap;
    va_start(ap,formatp);
    int chars = vpi_vprintf(formatp, ap);
    va_end(ap);
    return chars;
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* formatp, va_list ap) {
    return VL_VPRINTF(formatp, ap);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8 *format, va_list ap) {
    FILE* fp = VL_CVT_I_FP(mcd);
    if (VL_UNLIKELY(!fp)) return 0;
    int chars = vfprintf(fp, format, ap);
    return chars;
}

PLI_INT32 vpi_flush(void) {
    Verilated::flushCall();
    return 0;
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
    FILE* fp = VL_CVT_I_FP(mcd);
    if (VL_UNLIKELY(!fp)) return 1;
    fflush(fp);
    return 0;
}

// utility routines

//-PLI_INT32 vpi_compare_objects(vpiHandle object1, vpiHandle object2) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-PLI_INT32 vpi_chk_error(p_vpi_error_info error_info_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

PLI_INT32 vpi_free_object(vpiHandle object) {
    return vpi_release_handle(object);  // Deprecated
}

PLI_INT32 vpi_release_handle (vpiHandle object) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_release_handle %p\n",object););
    VerilatedVpio* vop = VerilatedVpio::castp(object);
    if (VL_UNLIKELY(!vop)) return 0;
    vpi_remove_cb(object);  // May not be a callback, but that's ok
    delete vop;
    return 1;
}

//-PLI_INT32 vpi_get_vlog_info(p_vpi_vlog_info vlog_info_p) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

// routines added with 1364-2001

//-PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8 *dataLoc, PLI_INT32 numOfBytes) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8 *dataLoc, PLI_INT32 numOfBytes) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-void *vpi_get_userdata(vpiHandle obj) {
//-    _VL_VPI_UNIMP(); return 0;
//-}
//-PLI_INT32 vpi_put_userdata(vpiHandle obj, void *userdata) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

PLI_INT32 vpi_control(PLI_INT32 operation, ...) {
    VL_DEBUG_IF_PLI(VL_PRINTF("-vltVpi:  vpi_control %d\n",operation););
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
    _VL_VPI_UNIMP(); return 0;
}

//-vpiHandle vpi_handle_by_multi_index(vpiHandle obj, PLI_INT32 num_index, PLI_INT32 *index_array) {
//-    _VL_VPI_UNIMP(); return 0;
//-}

//======================================================================

#endif // Guard
