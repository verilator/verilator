// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated common data type containers
///
/// verilated.h should be included instead of this file.
///
/// Those macro/function/variable starting or ending in _ are internal,
/// however many of the other function/macros here are also internal.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_TYPES_H_
#define VERILATOR_VERILATED_TYPES_H_

#ifndef VERILATOR_VERILATED_H_INTERNAL_
#error "verilated_types.h should only be included by verilated.h"
#endif

#include <algorithm>
#include <deque>
#include <map>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>

//===================================================================
// String formatters (required by below containers)

extern std::string VL_TO_STRING(CData lhs);
extern std::string VL_TO_STRING(SData lhs);
extern std::string VL_TO_STRING(IData lhs);
extern std::string VL_TO_STRING(QData lhs);
inline std::string VL_TO_STRING(const std::string& obj) { return "\"" + obj + "\""; }
extern std::string VL_TO_STRING_W(int words, const WDataInP obj);

//=========================================================================
// Declare net data types

#define VL_SIG8(name, msb, lsb) CData name  ///< Declare signal, 1-8 bits
#define VL_SIG16(name, msb, lsb) SData name  ///< Declare signal, 9-16 bits
#define VL_SIG64(name, msb, lsb) QData name  ///< Declare signal, 33-64 bits
#define VL_SIG(name, msb, lsb) IData name  ///< Declare signal, 17-32 bits
#define VL_SIGW(name, msb, lsb, words) VlWide<words> name  ///< Declare signal, 65+ bits
#define VL_IN8(name, msb, lsb) CData name  ///< Declare input signal, 1-8 bits
#define VL_IN16(name, msb, lsb) SData name  ///< Declare input signal, 9-16 bits
#define VL_IN64(name, msb, lsb) QData name  ///< Declare input signal, 33-64 bits
#define VL_IN(name, msb, lsb) IData name  ///< Declare input signal, 17-32 bits
#define VL_INW(name, msb, lsb, words) VlWide<words> name  ///< Declare input signal, 65+ bits
#define VL_INOUT8(name, msb, lsb) CData name  ///< Declare bidir signal, 1-8 bits
#define VL_INOUT16(name, msb, lsb) SData name  ///< Declare bidir signal, 9-16 bits
#define VL_INOUT64(name, msb, lsb) QData name  ///< Declare bidir signal, 33-64 bits
#define VL_INOUT(name, msb, lsb) IData name  ///< Declare bidir signal, 17-32 bits
#define VL_INOUTW(name, msb, lsb, words) VlWide<words> name  ///< Declare bidir signal, 65+ bits
#define VL_OUT8(name, msb, lsb) CData name  ///< Declare output signal, 1-8 bits
#define VL_OUT16(name, msb, lsb) SData name  ///< Declare output signal, 9-16 bits
#define VL_OUT64(name, msb, lsb) QData name  ///< Declare output signal, 33-64bits
#define VL_OUT(name, msb, lsb) IData name  ///< Declare output signal, 17-32 bits
#define VL_OUTW(name, msb, lsb, words) VlWide<words> name  ///< Declare output signal, 65+ bits

//===================================================================
// Shuffle RNG

extern uint64_t vl_rand64() VL_MT_SAFE;

class VlURNG final {
public:
    using result_type = size_t;
    static constexpr size_t min() { return 0; }
    static constexpr size_t max() { return 1ULL << 31; }
    size_t operator()() { return VL_MASK_I(31) & vl_rand64(); }
};

//===================================================================
// Readmem/Writemem operation classes

class VlReadMem final {
    const bool m_hex;  // Hex format
    const int m_bits;  // Bit width of values
    const std::string& m_filename;  // Filename
    const QData m_end;  // End address (as specified by user)
    FILE* m_fp = nullptr;  // File handle for filename
    QData m_addr = 0;  // Next address to read
    int m_linenum = 0;  // Line number last read from file
    bool m_anyAddr = false;  // Had address directive in the file
public:
    VlReadMem(bool hex, int bits, const std::string& filename, QData start, QData end);
    ~VlReadMem();
    bool isOpen() const { return m_fp != nullptr; }
    int linenum() const { return m_linenum; }
    bool get(QData& addrr, std::string& valuer);
    void setData(void* valuep, const std::string& rhs);
};

class VlWriteMem final {
    const bool m_hex;  // Hex format
    const int m_bits;  // Bit width of values
    FILE* m_fp = nullptr;  // File handle for filename
    QData m_addr = 0;  // Next address to write
public:
    VlWriteMem(bool hex, int bits, const std::string& filename, QData start, QData end);
    ~VlWriteMem();
    bool isOpen() const { return m_fp != nullptr; }
    void print(QData addr, bool addrstamp, const void* valuep);
};

//===================================================================
/// Verilog wide packed bit container.
/// Similar to std::array<WData, N>, but lighter weight, only methods needed
/// by Verilator, to help compile time.
///
/// A 'struct' as we want this to be an aggregate type that allows
/// static aggregate initialization. Consider data members private.
///
/// For example a Verilog "bit [94:0]" will become a VlWide<3> because 3*32
/// bits are needed to hold the 95 bits. The MSB (bit 96) must always be
/// zero in memory, but during intermediate operations in the Verilated
/// internals is unpredictable.

static int _vl_cmp_w(int words, WDataInP const lwp, WDataInP const rwp) VL_MT_SAFE;

template <std::size_t T_Words>
struct VlWide final {
    // MEMBERS
    // This should be the only data member, otherwise generated static initializers need updating
    EData m_storage[T_Words];  // Contents of the packed array

    // CONSTRUCTORS
    // Default constructors and destructor are used. Note however that C++20 requires that
    // aggregate types do not have a user declared constructor, not even an explicitly defaulted
    // one.

    // OPERATOR METHODS
    // Default copy assignment operators are used.
    operator WDataOutP() { return &m_storage[0]; }  // This also allows []
    operator WDataInP() const { return &m_storage[0]; }  // This also allows []

    // METHODS
    const EData& at(size_t index) const { return m_storage[index]; }
    EData& at(size_t index) { return m_storage[index]; }
    WData* data() { return &m_storage[0]; }
    const WData* data() const { return &m_storage[0]; }
    bool operator<(const VlWide<T_Words>& rhs) const {
        return _vl_cmp_w(T_Words, data(), rhs.data()) < 0;
    }
};

// Convert a C array to std::array reference by pointer magic, without copy.
// Data type (second argument) is so the function template can automatically generate.
template <std::size_t T_Words>
VlWide<T_Words>& VL_CVT_W_A(const WDataInP inp, const VlWide<T_Words>&) {
    return *((VlWide<T_Words>*)inp);
}

template <std::size_t T_Words>
std::string VL_TO_STRING(const VlWide<T_Words>& obj) {
    return VL_TO_STRING_W(T_Words, obj.data());
}

//===================================================================
// Verilog queue and dynamic array container
// There are no multithreaded locks on this; the base variable must
// be protected by other means
//
// Bound here is the maximum size() allowed, e.g. 1 + SystemVerilog bound
// For dynamic arrays it is always zero
template <class T_Value, size_t T_MaxSize = 0>
class VlQueue final {
private:
    // TYPES
    using Deque = std::deque<T_Value>;

public:
    using const_iterator = typename Deque::const_iterator;

private:
    // MEMBERS
    Deque m_deque;  // State of the assoc array
    T_Value m_defaultValue;  // Default value

public:
    // CONSTRUCTORS
    // m_defaultValue isn't defaulted. Caller's constructor must do it.
    VlQueue() = default;
    ~VlQueue() = default;
    VlQueue(const VlQueue&) = default;
    VlQueue(VlQueue&&) = default;
    VlQueue& operator=(const VlQueue&) = default;
    VlQueue& operator=(VlQueue&&) = default;

    // Standard copy constructor works. Verilog: assoca = assocb
    // Also must allow conversion from a different T_MaxSize queue
    template <size_t U_MaxSize = 0>
    VlQueue operator=(const VlQueue<T_Value, U_MaxSize>& rhs) {
        m_deque = rhs.privateDeque();
        if (VL_UNLIKELY(T_MaxSize && T_MaxSize < m_deque.size())) m_deque.resize(T_MaxSize - 1);
        return *this;
    }

    static VlQueue cons(const T_Value& lhs) {
        VlQueue out;
        out.push_back(lhs);
        return out;
    }
    static VlQueue cons(const T_Value& lhs, const T_Value& rhs) {
        VlQueue out;
        out.push_back(rhs);
        out.push_back(lhs);
        return out;
    }
    static VlQueue cons(const VlQueue& lhs, const T_Value& rhs) {
        VlQueue out = lhs;
        out.push_front(rhs);
        return out;
    }
    static VlQueue cons(const T_Value& lhs, const VlQueue& rhs) {
        VlQueue out = rhs;
        out.push_back(lhs);
        return out;
    }
    static VlQueue cons(const VlQueue& lhs, const VlQueue& rhs) {
        VlQueue out = rhs;
        for (const auto& i : lhs.m_deque) out.push_back(i);
        return out;
    }

    // METHODS
    T_Value& atDefault() { return m_defaultValue; }
    const T_Value& atDefault() const { return m_defaultValue; }
    const Deque& privateDeque() const { return m_deque; }

    // Size. Verilog: function int size(), or int num()
    int size() const { return m_deque.size(); }
    // Clear array. Verilog: function void delete([input index])
    void clear() { m_deque.clear(); }
    void erase(int32_t index) {
        if (VL_LIKELY(index >= 0 && index < m_deque.size()))
            m_deque.erase(m_deque.begin() + index);
    }

    // Dynamic array new[] becomes a renew()
    void renew(size_t size) {
        clear();
        m_deque.resize(size, atDefault());
    }
    // Dynamic array new[]() becomes a renew_copy()
    void renew_copy(size_t size, const VlQueue<T_Value, T_MaxSize>& rhs) {
        if (size == 0) {
            clear();
        } else {
            *this = rhs;
            m_deque.resize(size, atDefault());
        }
    }

    // function void q.push_front(value)
    void push_front(const T_Value& value) {
        m_deque.push_front(value);
        if (VL_UNLIKELY(T_MaxSize != 0 && m_deque.size() > T_MaxSize)) m_deque.pop_back();
    }
    // function void q.push_back(value)
    void push_back(const T_Value& value) {
        if (VL_LIKELY(T_MaxSize == 0 || m_deque.size() < T_MaxSize)) m_deque.push_back(value);
    }
    // function value_t q.pop_front();
    T_Value pop_front() {
        if (m_deque.empty()) return m_defaultValue;
        T_Value v = m_deque.front();
        m_deque.pop_front();
        return v;
    }
    // function value_t q.pop_back();
    T_Value pop_back() {
        if (m_deque.empty()) return m_defaultValue;
        T_Value v = m_deque.back();
        m_deque.pop_back();
        return v;
    }

    // Setting. Verilog: assoc[index] = v
    // Can't just overload operator[] or provide a "at" reference to set,
    // because we need to be able to insert only when the value is set
    T_Value& at(int32_t index) {
        static VL_THREAD_LOCAL T_Value s_throwAway;
        // Needs to work for dynamic arrays, so does not use T_MaxSize
        if (VL_UNLIKELY(index < 0 || index >= m_deque.size())) {
            s_throwAway = atDefault();
            return s_throwAway;
        } else {
            return m_deque[index];
        }
    }
    // Accessing. Verilog: v = assoc[index]
    const T_Value& at(int32_t index) const {
        static VL_THREAD_LOCAL T_Value s_throwAway;
        // Needs to work for dynamic arrays, so does not use T_MaxSize
        if (VL_UNLIKELY(index < 0 || index >= m_deque.size())) {
            return atDefault();
        } else {
            return m_deque[index];
        }
    }
    // function void q.insert(index, value);
    void insert(int32_t index, const T_Value& value) {
        if (VL_UNLIKELY(index < 0 || index >= m_deque.size())) return;
        m_deque.insert(m_deque.begin() + index, value);
    }

    // Return slice q[lsb:msb]
    VlQueue slice(int32_t lsb, int32_t msb) const {
        VlQueue out;
        if (VL_UNLIKELY(lsb < 0)) lsb = 0;
        if (VL_UNLIKELY(lsb >= m_deque.size())) lsb = m_deque.size() - 1;
        if (VL_UNLIKELY(msb >= m_deque.size())) msb = m_deque.size() - 1;
        for (int32_t i = lsb; i <= msb; ++i) out.push_back(m_deque[i]);
        return out;
    }

    // For save/restore
    const_iterator begin() const { return m_deque.begin(); }
    const_iterator end() const { return m_deque.end(); }

    // Methods
    void sort() { std::sort(m_deque.begin(), m_deque.end()); }
    template <typename Func>
    void sort(Func with_func) {
        // with_func returns arbitrary type to use for the sort comparison
        std::sort(m_deque.begin(), m_deque.end(), [=](const T_Value& a, const T_Value& b) {
            // index number is meaninless with sort, as it changes
            return with_func(0, a) < with_func(0, b);
        });
    }
    void rsort() { std::sort(m_deque.rbegin(), m_deque.rend()); }
    template <typename Func>
    void rsort(Func with_func) {
        // with_func returns arbitrary type to use for the sort comparison
        std::sort(m_deque.rbegin(), m_deque.rend(), [=](const T_Value& a, const T_Value& b) {
            // index number is meaninless with sort, as it changes
            return with_func(0, a) < with_func(0, b);
        });
    }
    void reverse() { std::reverse(m_deque.begin(), m_deque.end()); }
    void shuffle() { std::shuffle(m_deque.begin(), m_deque.end(), VlURNG{}); }
    VlQueue unique() const {
        VlQueue out;
        std::unordered_set<T_Value> saw;
        for (const auto& i : m_deque) {
            auto it = saw.find(i);
            if (it == saw.end()) {
                saw.insert(it, i);
                out.push_back(i);
            }
        }
        return out;
    }
    VlQueue<IData> unique_index() const {
        VlQueue<IData> out;
        IData index = 0;
        std::unordered_set<T_Value> saw;
        for (const auto& i : m_deque) {
            auto it = saw.find(i);
            if (it == saw.end()) {
                saw.insert(it, i);
                out.push_back(index);
            }
            ++index;
        }
        return out;
    }
    template <typename Func>
    VlQueue find(Func with_func) const {
        VlQueue out;
        IData index = 0;
        for (const auto& i : m_deque) {
            if (with_func(index, i)) out.push_back(i);
            ++index;
        }
        return out;
    }
    template <typename Func>
    VlQueue<IData> find_index(Func with_func) const {
        VlQueue<IData> out;
        IData index = 0;
        for (const auto& i : m_deque) {
            if (with_func(index, i)) out.push_back(index);
            ++index;
        }
        return out;
    }
    template <typename Func>
    VlQueue find_first(Func with_func) const {
        // Can't use std::find_if as need index number
        IData index = 0;
        for (const auto& i : m_deque) {
            if (with_func(index, i)) return VlQueue::cons(i);
            ++index;
        }
        return VlQueue{};
    }
    template <typename Func>
    VlQueue<IData> find_first_index(Func with_func) const {
        IData index = 0;
        for (const auto& i : m_deque) {
            if (with_func(index, i)) return VlQueue<IData>::cons(index);
            ++index;
        }
        return VlQueue<IData>{};
    }
    template <typename Func>
    VlQueue find_last(Func with_func) const {
        IData index = m_deque.size() - 1;
        for (auto& item : vlstd::reverse_view(m_deque)) {
            if (with_func(index, item)) return VlQueue::cons(item);
            --index;
        }
        return VlQueue{};
    }
    template <typename Func>
    VlQueue<IData> find_last_index(Func with_func) const {
        IData index = m_deque.size() - 1;
        for (auto& item : vlstd::reverse_view(m_deque)) {
            if (with_func(index, item)) return VlQueue<IData>::cons(index);
            --index;
        }
        return VlQueue<IData>{};
    }

    // Reduction operators
    VlQueue min() const {
        if (m_deque.empty()) return VlQueue{};
        const auto it = std::min_element(m_deque.begin(), m_deque.end());
        return VlQueue::cons(*it);
    }
    VlQueue max() const {
        if (m_deque.empty()) return VlQueue{};
        const auto it = std::max_element(m_deque.begin(), m_deque.end());
        return VlQueue::cons(*it);
    }

    T_Value r_sum() const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_deque) out += i;
        return out;
    }
    template <typename Func>
    T_Value r_sum(Func with_func) const {
        T_Value out(0);  // Type must have assignment operator
        IData index = 0;
        for (const auto& i : m_deque) out += with_func(index++, i);
        return out;
    }
    T_Value r_product() const {
        if (m_deque.empty()) return T_Value(0);
        auto it = m_deque.begin();
        T_Value out{*it};
        ++it;
        for (; it != m_deque.end(); ++it) out *= *it;
        return out;
    }
    template <typename Func>
    T_Value r_product(Func with_func) const {
        if (m_deque.empty()) return T_Value(0);
        auto it = m_deque.begin();
        IData index = 0;
        T_Value out{with_func(index, *it)};
        ++it;
        ++index;
        for (; it != m_deque.end(); ++it) out *= with_func(index++, *it);
        return out;
    }
    T_Value r_and() const {
        if (m_deque.empty()) return T_Value(0);
        auto it = m_deque.begin();
        T_Value out{*it};
        ++it;
        for (; it != m_deque.end(); ++it) out &= *it;
        return out;
    }
    template <typename Func>
    T_Value r_and(Func with_func) const {
        if (m_deque.empty()) return T_Value(0);
        auto it = m_deque.begin();
        IData index = 0;
        T_Value out{with_func(index, *it)};
        ++it;
        ++index;
        for (; it != m_deque.end(); ++it) out &= with_func(index, *it);
        return out;
    }
    T_Value r_or() const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_deque) out |= i;
        return out;
    }
    template <typename Func>
    T_Value r_or(Func with_func) const {
        T_Value out(0);  // Type must have assignment operator
        IData index = 0;
        for (const auto& i : m_deque) out |= with_func(index++, i);
        return out;
    }
    T_Value r_xor() const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_deque) out ^= i;
        return out;
    }
    template <typename Func>
    T_Value r_xor(Func with_func) const {
        T_Value out(0);  // Type must have assignment operator
        IData index = 0;
        for (const auto& i : m_deque) out ^= with_func(index++, i);
        return out;
    }

    // Dumping. Verilog: str = $sformatf("%p", assoc)
    std::string to_string() const {
        if (m_deque.empty()) return "'{}";  // No trailing space
        std::string out = "'{";
        std::string comma;
        for (const auto& i : m_deque) {
            out += comma + VL_TO_STRING(i);
            comma = ", ";
        }
        return out + "} ";
    }
};

template <class T_Value>
std::string VL_TO_STRING(const VlQueue<T_Value>& obj) {
    return obj.to_string();
}

//===================================================================
// Verilog associative array container
// There are no multithreaded locks on this; the base variable must
// be protected by other means
//
template <class T_Key, class T_Value>
class VlAssocArray final {
private:
    // TYPES
    using Map = std::map<T_Key, T_Value>;

public:
    using const_iterator = typename Map::const_iterator;

private:
    // MEMBERS
    Map m_map;  // State of the assoc array
    T_Value m_defaultValue;  // Default value

public:
    // CONSTRUCTORS
    // m_defaultValue isn't defaulted. Caller's constructor must do it.
    VlAssocArray() = default;
    ~VlAssocArray() = default;
    VlAssocArray(const VlAssocArray&) = default;
    VlAssocArray(VlAssocArray&&) = default;
    VlAssocArray& operator=(const VlAssocArray&) = default;
    VlAssocArray& operator=(VlAssocArray&&) = default;

    // METHODS
    T_Value& atDefault() { return m_defaultValue; }
    const T_Value& atDefault() const { return m_defaultValue; }

    // Size of array. Verilog: function int size(), or int num()
    int size() const { return m_map.size(); }
    // Clear array. Verilog: function void delete([input index])
    void clear() { m_map.clear(); }
    void erase(const T_Key& index) { m_map.erase(index); }
    // Return 0/1 if element exists. Verilog: function int exists(input index)
    int exists(const T_Key& index) const { return m_map.find(index) != m_map.end(); }
    // Return first element.  Verilog: function int first(ref index);
    int first(T_Key& indexr) const {
        const auto it = m_map.cbegin();
        if (it == m_map.end()) return 0;
        indexr = it->first;
        return 1;
    }
    // Return last element.  Verilog: function int last(ref index)
    int last(T_Key& indexr) const {
        const auto it = m_map.crbegin();
        if (it == m_map.rend()) return 0;
        indexr = it->first;
        return 1;
    }
    // Return next element. Verilog: function int next(ref index)
    int next(T_Key& indexr) const {
        auto it = m_map.find(indexr);
        if (VL_UNLIKELY(it == m_map.end())) return 0;
        ++it;
        if (VL_UNLIKELY(it == m_map.end())) return 0;
        indexr = it->first;
        return 1;
    }
    // Return prev element. Verilog: function int prev(ref index)
    int prev(T_Key& indexr) const {
        auto it = m_map.find(indexr);
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
        const auto it = m_map.find(index);
        if (it == m_map.end()) {
            std::pair<typename Map::iterator, bool> pit = m_map.emplace(index, m_defaultValue);
            return pit.first->second;
        }
        return it->second;
    }
    // Accessing. Verilog: v = assoc[index]
    const T_Value& at(const T_Key& index) const {
        const auto it = m_map.find(index);
        if (it == m_map.end()) {
            return m_defaultValue;
        } else {
            return it->second;
        }
    }
    // Setting as a chained operation
    VlAssocArray& set(const T_Key& index, const T_Value& value) {
        at(index) = value;
        return *this;
    }
    VlAssocArray& setDefault(const T_Value& value) {
        atDefault() = value;
        return *this;
    }

    // For save/restore
    const_iterator begin() const { return m_map.begin(); }
    const_iterator end() const { return m_map.end(); }

    // Methods
    VlQueue<T_Value> unique() const {
        VlQueue<T_Value> out;
        std::set<T_Value> saw;
        for (const auto& i : m_map) {
            auto it = saw.find(i.second);
            if (it == saw.end()) {
                saw.insert(it, i.second);
                out.push_back(i.second);
            }
        }
        return out;
    }
    VlQueue<T_Key> unique_index() const {
        VlQueue<T_Key> out;
        std::set<T_Key> saw;
        for (const auto& i : m_map) {
            auto it = saw.find(i.second);
            if (it == saw.end()) {
                saw.insert(it, i.second);
                out.push_back(i.first);
            }
        }
        return out;
    }
    template <typename Func>
    VlQueue<T_Value> find(Func with_func) const {
        VlQueue<T_Value> out;
        for (const auto& i : m_map)
            if (with_func(i.first, i.second)) out.push_back(i.second);
        return out;
    }
    template <typename Func>
    VlQueue<T_Key> find_index(Func with_func) const {
        VlQueue<T_Key> out;
        for (const auto& i : m_map)
            if (with_func(i.first, i.second)) out.push_back(i.first);
        return out;
    }
    template <typename Func>
    VlQueue<T_Value> find_first(Func with_func) const {
        const auto it
            = std::find_if(m_map.begin(), m_map.end(), [=](const std::pair<T_Key, T_Value>& i) {
                  return with_func(i.first, i.second);
              });
        if (it == m_map.end()) return VlQueue<T_Value>{};
        return VlQueue<T_Value>::cons(it->second);
    }
    template <typename Func>
    VlQueue<T_Key> find_first_index(Func with_func) const {
        const auto it
            = std::find_if(m_map.begin(), m_map.end(), [=](const std::pair<T_Key, T_Value>& i) {
                  return with_func(i.first, i.second);
              });
        if (it == m_map.end()) return VlQueue<T_Value>{};
        return VlQueue<T_Key>::cons(it->first);
    }
    template <typename Func>
    VlQueue<T_Value> find_last(Func with_func) const {
        const auto it
            = std::find_if(m_map.rbegin(), m_map.rend(), [=](const std::pair<T_Key, T_Value>& i) {
                  return with_func(i.first, i.second);
              });
        if (it == m_map.rend()) return VlQueue<T_Value>{};
        return VlQueue<T_Value>::cons(it->second);
    }
    template <typename Func>
    VlQueue<T_Key> find_last_index(Func with_func) const {
        const auto it
            = std::find_if(m_map.rbegin(), m_map.rend(), [=](const std::pair<T_Key, T_Value>& i) {
                  return with_func(i.first, i.second);
              });
        if (it == m_map.rend()) return VlQueue<T_Value>{};
        return VlQueue<T_Key>::cons(it->first);
    }

    // Reduction operators
    VlQueue<T_Value> min() const {
        if (m_map.empty()) return VlQueue<T_Value>();
        const auto it = std::min_element(
            m_map.begin(), m_map.end(),
            [](const std::pair<T_Key, T_Value>& a, const std::pair<T_Key, T_Value>& b) {
                return a.second < b.second;
            });
        return VlQueue<T_Value>::cons(it->second);
    }
    VlQueue<T_Value> max() const {
        if (m_map.empty()) return VlQueue<T_Value>();
        const auto it = std::max_element(
            m_map.begin(), m_map.end(),
            [](const std::pair<T_Key, T_Value>& a, const std::pair<T_Key, T_Value>& b) {
                return a.second < b.second;
            });
        return VlQueue<T_Value>::cons(it->second);
    }

    T_Value r_sum() const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_map) out += i.second;
        return out;
    }
    template <typename Func>
    T_Value r_sum(Func with_func) const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_map) out += with_func(i.first, i.second);
        return out;
    }
    T_Value r_product() const {
        if (m_map.empty()) return T_Value(0);
        auto it = m_map.begin();
        T_Value out{it->second};
        ++it;
        for (; it != m_map.end(); ++it) out *= it->second;
        return out;
    }
    template <typename Func>
    T_Value r_product(Func with_func) const {
        if (m_map.empty()) return T_Value(0);
        auto it = m_map.begin();
        T_Value out{with_func(it->first, it->second)};
        ++it;
        for (; it != m_map.end(); ++it) out *= with_func(it->first, it->second);
        return out;
    }
    T_Value r_and() const {
        if (m_map.empty()) return T_Value(0);
        auto it = m_map.begin();
        T_Value out{it->second};
        ++it;
        for (; it != m_map.end(); ++it) out &= it->second;
        return out;
    }
    template <typename Func>
    T_Value r_and(Func with_func) const {
        if (m_map.empty()) return T_Value(0);
        auto it = m_map.begin();
        T_Value out{with_func(it->first, it->second)};
        ++it;
        for (; it != m_map.end(); ++it) out &= with_func(it->first, it->second);
        return out;
    }
    T_Value r_or() const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_map) out |= i.second;
        return out;
    }
    template <typename Func>
    T_Value r_or(Func with_func) const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_map) out |= with_func(i.first, i.second);
        return out;
    }
    T_Value r_xor() const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_map) out ^= i.second;
        return out;
    }
    template <typename Func>
    T_Value r_xor(Func with_func) const {
        T_Value out(0);  // Type must have assignment operator
        for (const auto& i : m_map) out ^= with_func(i.first, i.second);
        return out;
    }

    // Dumping. Verilog: str = $sformatf("%p", assoc)
    std::string to_string() const {
        if (m_map.empty()) return "'{}";  // No trailing space
        std::string out = "'{";
        std::string comma;
        for (const auto& i : m_map) {
            out += comma + VL_TO_STRING(i.first) + ":" + VL_TO_STRING(i.second);
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

template <class T_Key, class T_Value>
void VL_READMEM_N(bool hex, int bits, const std::string& filename,
                  VlAssocArray<T_Key, T_Value>& obj, QData start, QData end) VL_MT_SAFE {
    VlReadMem rmem{hex, bits, filename, start, end};
    if (VL_UNLIKELY(!rmem.isOpen())) return;
    while (true) {
        QData addr;
        std::string data;
        if (rmem.get(addr /*ref*/, data /*ref*/)) {
            rmem.setData(&(obj.at(addr)), data);
        } else {
            break;
        }
    }
}

template <class T_Key, class T_Value>
void VL_WRITEMEM_N(bool hex, int bits, const std::string& filename,
                   const VlAssocArray<T_Key, T_Value>& obj, QData start, QData end) VL_MT_SAFE {
    VlWriteMem wmem{hex, bits, filename, start, end};
    if (VL_UNLIKELY(!wmem.isOpen())) return;
    for (const auto& i : obj) {
        const QData addr = i.first;
        if (addr >= start && addr <= end) wmem.print(addr, true, &(i.second));
    }
}

//===================================================================
/// Verilog unpacked array container
/// For when a standard C++[] array is not sufficient, e.g. an
/// array under a queue, or methods operating on the array.
///
/// A 'struct' as we want this to be an aggregate type that allows
/// static aggregate initialization. Consider data members private.
///
/// This class may get exposed to a Verilated Model's top I/O, if the top
/// IO has an unpacked array.

template <class T_Value, std::size_t T_Depth>
struct VlUnpacked final {
    // MEMBERS
    // This should be the only data member, otherwise generated static initializers need updating
    T_Value m_storage[T_Depth];  // Contents of the unpacked array

    // CONSTRUCTORS
    // Default constructors and destructor are used. Note however that C++20 requires that
    // aggregate types do not have a user declared constructor, not even an explicitly defaulted
    // one.

    // OPERATOR METHODS
    // Default copy assignment operators are used.

    // METHODS
    // Raw access
    WData* data() { return &m_storage[0]; }
    const WData* data() const { return &m_storage[0]; }

    T_Value& operator[](size_t index) { return m_storage[index]; }
    const T_Value& operator[](size_t index) const { return m_storage[index]; }

    // Dumping. Verilog: str = $sformatf("%p", assoc)
    std::string to_string() const {
        std::string out = "'{";
        std::string comma;
        for (int i = 0; i < T_Depth; ++i) {
            out += comma + VL_TO_STRING(m_storage[i]);
            comma = ", ";
        }
        return out + "} ";
    }
};

template <class T_Value, std::size_t T_Depth>
std::string VL_TO_STRING(const VlUnpacked<T_Value, T_Depth>& obj) {
    return obj.to_string();
}

//===================================================================
// Verilog class reference container
// There are no multithreaded locks on this; the base variable must
// be protected by other means

#define VlClassRef std::shared_ptr

template <class T>  // T typically of type VlClassRef<x>
inline T VL_NULL_CHECK(T t, const char* filename, int linenum) {
    if (VL_UNLIKELY(!t)) Verilated::nullPointerError(filename, linenum);
    return t;
}

template <typename T, typename U>
static inline bool VL_CAST_DYNAMIC(VlClassRef<T> in, VlClassRef<U>& outr) {
    VlClassRef<U> casted = std::dynamic_pointer_cast<U>(in);
    if (VL_LIKELY(casted)) {
        outr = casted;
        return true;
    } else {
        return false;
    }
}

//======================================================================

#endif  // Guard
