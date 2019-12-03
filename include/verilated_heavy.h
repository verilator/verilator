// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2019 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
///
/// \file
/// \brief Verilator: String include for all Verilated C files
///
///     This file is included automatically by Verilator at the top of
///     all C++ files it generates.  It is used when strings or other
///     heavyweight types are required; these contents are not part of
///     verilated.h to save compile time when such types aren't used.
///
/// Code available from: https://verilator.org
///
//*************************************************************************

#ifndef _VERILATED_HEAVY_H_
#define _VERILATED_HEAVY_H_ 1  ///< Header Guard

#include "verilated.h"

#include <deque>
#include <map>
#include <string>

//===================================================================
// String formatters (required by below containers)

extern std::string VL_TO_STRING(CData obj);
extern std::string VL_TO_STRING(SData obj);
extern std::string VL_TO_STRING(IData obj);
extern std::string VL_TO_STRING(QData obj);
inline std::string VL_TO_STRING(const std::string& obj) { return "\""+obj+"\""; }

//===================================================================
// Verilog array container
// Similar to std::array<WData, N>, but:
//   1. Doesn't require C++11
//   2. Lighter weight, only methods needed by Verilator, to help compile time.
//
// This is only used when we need an upper-level container and so can't
// simply use a C style array (which is just a pointer).

template <std::size_t T_Words> class VlWide {
    WData m_storage[T_Words];
public:
    // Default constructor/destructor/copy are fine
    const WData& at(size_t index) const { return m_storage[index]; }
    WData& at(size_t index) { return m_storage[index]; }
    WData* data() { return &m_storage[0]; }
    const WData* data() const { return &m_storage[0]; }
    bool operator<(const VlWide<T_Words>& rhs) const {
        return VL_LT_W(T_Words, data(), rhs.data());
    }
};

// Convert a C array to std::array reference by pointer magic, without copy.
// Data type (second argument) is so the function template can automatically generate.
template <std::size_t T_Words>
VlWide<T_Words>& VL_CVT_W_A(WDataInP inp, const VlWide<T_Words>&) {
    return *((VlWide<T_Words>*)inp);
}


//===================================================================
// Verilog associative array container
// There are no multithreaded locks on this; the base variable must
// be protected by other means
//
template <class T_Key, class T_Value> class VlAssocArray {
private:
    // TYPES
    typedef std::map<T_Key, T_Value> Map;
public:
    typedef typename Map::const_iterator const_iterator;

private:
    // MEMBERS
    Map m_map;  // State of the assoc array
    T_Value m_defaultValue;  // Default value

public:
    // CONSTRUCTORS
    VlAssocArray() {
        // m_defaultValue isn't defaulted. Caller's constructor must do it.
    }
    ~VlAssocArray() {}
    // Standard copy constructor works. Verilog: assoca = assocb

    // METHODS
    T_Value& atDefault() { return m_defaultValue; }

    // Size of array. Verilog: function int size(), or int num()
    int size() const { return m_map.size(); }
    // Clear array. Verilog: function void delete([input index])
    void clear() { m_map.clear(); }
    void erase(const T_Key& index) { m_map.erase(index); }
    // Return 0/1 if element exists. Verilog: function int exists(input index)
    int exists(const T_Key& index) const { return m_map.find(index) != m_map.end(); }
    // Return first element.  Verilog: function int first(ref index);
    int first(T_Key& indexr) const {
        typename Map::const_iterator it = m_map.begin();
        if (it == m_map.end()) return 0;
        indexr = it->first;
        return 1;
    }
    // Return last element.  Verilog: function int last(ref index)
    int last(T_Key& indexr) const {
        typename Map::const_reverse_iterator it = m_map.rbegin();
        if (it == m_map.rend()) return 0;
        indexr = it->first;
        return 1;
    }
    // Return next element. Verilog: function int next(ref index)
    int next(T_Key& indexr) const {
        typename Map::const_iterator it = m_map.find(indexr);
        if (VL_UNLIKELY(it == m_map.end())) return 0;
        it++;
        if (VL_UNLIKELY(it == m_map.end())) return 0;
        indexr = it->first;
        return 1;
    }
    // Return prev element. Verilog: function int prev(ref index)
    int prev(T_Key& indexr) const {
        typename Map::const_iterator it = m_map.find(indexr);
        if (VL_UNLIKELY(it == m_map.end())) return 0;
        if (VL_UNLIKELY(it == m_map.begin())) return 0;
        --it;
        indexr = it->first;
        return 1;
    }
    // Setting. Verilog: assoc[index] = v
    // Can't just overload operator[] or provide a "at" reference to set,
    // because we need to be able to insert only when the value is set
    T_Value& at(const T_Key& index) {
        typename Map::iterator it = m_map.find(index);
        if (it == m_map.end()) {
            std::pair<typename Map::iterator, bool> pit
                = m_map.insert(std::make_pair(index, m_defaultValue));
            return pit.first->second;
        }
        return it->second;
    }
    // Accessing. Verilog: v = assoc[index]
    const T_Value& at(const T_Key& index) const {
        typename Map::iterator it = m_map.find(index);
        if (it == m_map.end()) return m_defaultValue;
        else return it->second;
    }
    // For save/restore
    const_iterator begin() const { return m_map.begin(); }
    const_iterator end() const { return m_map.end(); }

    // Dumping. Verilog: str = $sformatf("%p", assoc)
    std::string to_string() const {
        std::string out = "'{";
        std::string comma;
        for (typename Map::const_iterator it = m_map.begin(); it != m_map.end(); ++it) {
            out += comma + VL_TO_STRING(it->first) + ":" + VL_TO_STRING(it->second);
            comma = ", ";
        }
        // Default not printed - maybe random init data
        return out + "} ";
    }
};

template <class T_Key, class T_Value>
std::string VL_TO_STRING(const VlAssocArray<T_Key, T_Value>& obj) {
    return obj.to_string();
}

//===================================================================
// Verilog queue container
// There are no multithreaded locks on this; the base variable must
// be protected by other means
//
template <class T_Value> class VlQueue {
private:
    // TYPES
    typedef std::deque<T_Value> Deque;
public:
    typedef typename Deque::const_iterator const_iterator;

private:
    // MEMBERS
    Deque m_deque;  // State of the assoc array
    T_Value m_defaultValue;  // Default value

public:
    // CONSTRUCTORS
    VlQueue() {
        // m_defaultValue isn't defaulted. Caller's constructor must do it.
    }
    ~VlQueue() {}
    // Standard copy constructor works. Verilog: assoca = assocb

    // METHODS
    T_Value& atDefault() { return m_defaultValue; }

    // Size. Verilog: function int size(), or int num()
    int size() const { return m_deque.size(); }
    // Clear array. Verilog: function void delete([input index])
    void clear() { m_deque.clear(); }
    void erase(size_t index) { if (VL_LIKELY(index < m_deque.size())) m_deque.erase(index); }

    // function void q.push_front(value)
    void push_front(const T_Value& value) { m_deque.push_front(value); }
    // function void q.push_back(value)
    void push_back(const T_Value& value) { m_deque.push_back(value); }
    // function value_t q.pop_front();
    T_Value pop_front() {
        if (m_deque.empty()) return m_defaultValue;
        T_Value v = m_deque.front(); m_deque.pop_front(); return v;
    }
    // function value_t q.pop_back();
    T_Value pop_back() {
        if (m_deque.empty()) return m_defaultValue;
        T_Value v = m_deque.back(); m_deque.pop_back(); return v;
    }

    // Setting. Verilog: assoc[index] = v
    // Can't just overload operator[] or provide a "at" reference to set,
    // because we need to be able to insert only when the value is set
    T_Value& at(size_t index) {
        static T_Value s_throwAway;
        if (VL_UNLIKELY(index >= m_deque.size())) {
            s_throwAway = atDefault();
            return s_throwAway;
        }
        else return m_deque[index];
    }
    // Accessing. Verilog: v = assoc[index]
    const T_Value& at(size_t index) const {
        static T_Value s_throwAway;
        if (VL_UNLIKELY(index >= m_deque.size())) return atDefault();
        else return m_deque[index];
    }
    // function void q.insert(index, value);
    void insert(size_t index, const T_Value& value) {
        if (VL_UNLIKELY(index >= m_deque.size())) return;
        m_deque[index] = value;
    }

    // For save/restore
    const_iterator begin() const { return m_deque.begin(); }
    const_iterator end() const { return m_deque.end(); }

    // Dumping. Verilog: str = $sformatf("%p", assoc)
    std::string to_string() const {
        std::string out = "'{";
        std::string comma;
        for (typename Deque::const_iterator it = m_deque.begin(); it != m_deque.end(); ++it) {
            out += comma + VL_TO_STRING(*it);
            comma = ", ";
        }
        return out + "} ";
    }
};

template <class T_Value>
std::string VL_TO_STRING(const VlQueue<T_Value>& obj) {
    return obj.to_string();
}

//======================================================================
// Conversion functions

extern std::string VL_CVT_PACK_STR_NW(int lwords, WDataInP lwp) VL_MT_SAFE;
inline std::string VL_CVT_PACK_STR_NQ(QData lhs) VL_PURE {
    WData lw[2];  VL_SET_WQ(lw, lhs);
    return VL_CVT_PACK_STR_NW(2, lw);
}
inline std::string VL_CVT_PACK_STR_NN(const std::string& lhs) VL_PURE {
    return lhs;
}
inline std::string VL_CVT_PACK_STR_NI(IData lhs) VL_PURE {
    WData lw[1];  lw[0] = lhs;
    return VL_CVT_PACK_STR_NW(1, lw);
}
inline std::string VL_CONCATN_NNN(const std::string& lhs, const std::string& rhs) VL_PURE {
    return lhs + rhs;
}
inline std::string VL_REPLICATEN_NNQ(int,int,int, const std::string& lhs, IData rep) VL_PURE {
    std::string out; out.reserve(lhs.length() * rep);
    for (unsigned times=0; times<rep; ++times) out += lhs;
    return out;
}
inline std::string VL_REPLICATEN_NNI(int obits,int lbits,int rbits,
                                     const std::string& lhs, IData rep) VL_PURE {
    return VL_REPLICATEN_NNQ(obits,lbits,rbits,lhs,rep);
}

inline IData VL_LEN_IN(const std::string& ld) { return ld.length(); }
extern std::string VL_TOLOWER_NN(const std::string& ld);
extern std::string VL_TOUPPER_NN(const std::string& ld);

extern IData VL_FOPEN_NI(const std::string& filename, IData mode) VL_MT_SAFE;
extern void VL_READMEM_N(bool hex, int width, int depth, int array_lsb,
                         const std::string& filename,
                         void* memp, IData start, IData end) VL_MT_SAFE;
extern void VL_WRITEMEM_N(bool hex, int width, int depth, int array_lsb,
                          const std::string& filename,
                          const void* memp, IData start, IData end) VL_MT_SAFE;
extern IData VL_SSCANF_INX(int lbits, const std::string& ld,
                           const char* formatp, ...) VL_MT_SAFE;
extern void VL_SFORMAT_X(int obits_ignored, std::string& output,
                         const char* formatp, ...) VL_MT_SAFE;
extern std::string VL_SFORMATF_NX(const char* formatp, ...) VL_MT_SAFE;
extern IData VL_VALUEPLUSARGS_INW(int rbits, const std::string& ld, WDataOutP rwp) VL_MT_SAFE;
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, CData& rdr) VL_MT_SAFE {
    WData rwp[2];  // WData must always be at least 2
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, SData& rdr) VL_MT_SAFE {
    WData rwp[2];  // WData must always be at least 2
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INI(int rbits, const std::string& ld, IData& rdr) VL_MT_SAFE {
    WData rwp[2];  // WData must always be at least 2
    IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = rwp[0];
    return got;
}
inline IData VL_VALUEPLUSARGS_INQ(int rbits, const std::string& ld, QData& rdr) VL_MT_SAFE {
    WData rwp[2];
    IData got = VL_VALUEPLUSARGS_INW(rbits, ld, rwp);
    if (got) rdr = VL_SET_QW(rwp);
    return got;
}
inline IData VL_VALUEPLUSARGS_INQ(int rbits, const std::string& ld, double& rdr) VL_MT_SAFE {
    WData rwp[2];
    IData got = VL_VALUEPLUSARGS_INW(rbits,ld,rwp);
    if (got) rdr = VL_CVT_D_Q(VL_SET_QW(rwp));
    return got;
}
extern IData VL_VALUEPLUSARGS_INN(int, const std::string& ld, std::string& rdr) VL_MT_SAFE;

#endif  // Guard
