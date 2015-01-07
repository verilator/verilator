// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: List class with storage in existing classes
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef _V3LIST_H_
#define _V3LIST_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include <vector>

//============================================================================

template <class T> class V3List;
template <class T> class V3ListEnt;

template <class T>
class V3List {
    // List container for linked list of elements of type *T  (T is a pointer type)
private:
    // STATE
    T		m_headp;	// First element
    T		m_tailp;	// Last element
    friend class V3ListEnt<T>;
public:
    V3List()
	: m_headp(NULL), m_tailp(NULL) {}
    ~V3List() {}
    // METHODS
    T begin() const { return m_headp; }
    T end() const { return NULL; }
    bool empty() const { return m_headp==NULL; }
    void reset() { m_headp=NULL; m_tailp=NULL; }  // clear() without walking the list
};

//============================================================================

template <class T>
class V3ListEnt {
    // List entry for linked list of elements of type *T  (T is a pointer type)
private:
    // STATE
    T		m_nextp;	// Pointer to next element, NULL=end
    T		m_prevp;	// Pointer to previous element, NULL=beginning
    friend class V3List<T>;
    static V3ListEnt* baseToListEnt(void* newbasep, size_t offset) {
	// "this" must be a element inside of *basep
	// Use that to determine a structure offset, then apply to the new base
	// to get our new pointer information
	return (V3ListEnt*) ( ((vluint8_t*)newbasep) + offset);
    }
public:
    V3ListEnt()
	: m_nextp(NULL), m_prevp(NULL) {}
    ~V3ListEnt() {
#ifdef VL_DEBUG
	// Load bogus pointers so we can catch deletion bugs
	m_nextp = (T)1;
	m_prevp = (T)1;
#endif
    }
    T nextp() const { return m_nextp; }
    // METHODS
    void pushBack (V3List<T>& listr, T newp) {
	// "this" must be a element inside of *newp
	// cppcheck-suppress thisSubtraction
	size_t offset = (size_t)(vluint8_t*)(this) - (size_t)(vluint8_t*)(newp);
	m_nextp = NULL;
	if (!listr.m_headp) listr.m_headp = newp;
	m_prevp = listr.m_tailp;
	if (m_prevp) baseToListEnt(m_prevp,offset)->m_nextp = newp;
	listr.m_tailp = newp;
    }
    void pushFront (V3List<T>& listr, T newp) {
	// "this" must be a element inside of *newp
	// cppcheck-suppress thisSubtraction
	size_t offset = (size_t)(vluint8_t*)(this) - (size_t)(vluint8_t*)(newp);
	m_nextp = listr.m_headp;
	if (m_nextp) baseToListEnt(m_nextp,offset)->m_prevp = newp;
	listr.m_headp = newp;
	m_prevp = NULL;
	if (!listr.m_tailp) listr.m_tailp = newp;
    }
    // Unlink from side
    void unlink (V3List<T>& listr, T oldp) {
	// "this" must be a element inside of *oldp
	// cppcheck-suppress thisSubtraction
	size_t offset = (size_t)(vluint8_t*)(this) - (size_t)(vluint8_t*)(oldp);
	if (m_nextp) baseToListEnt(m_nextp,offset)->m_prevp = m_prevp;
	else listr.m_tailp = m_prevp;
	if (m_prevp) baseToListEnt(m_prevp,offset)->m_nextp = m_nextp;
	else listr.m_headp = m_nextp;
	m_prevp = m_nextp = NULL;
    }
};

//============================================================================

#endif // Guard
