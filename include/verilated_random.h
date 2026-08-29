// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated randomization header
///
/// This file is included automatically by Verilator in some of the C++ files
/// it generates if randomization features are used.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
/// See the internals documentation docs/internals.rst for details.
///
//*************************************************************************
#ifndef VERILATOR_VERILATED_RANDOM_H_
#define VERILATOR_VERILATED_RANDOM_H_

#include "verilated.h"

#include <initializer_list>
#include <iomanip>
#include <iostream>
#include <ostream>
#include <set>
#include <sstream>
#include <unordered_set>

//=============================================================================

// VlRandomExpr and subclasses represent expressions for the constraint solver.
class ArrayInfo final {
public:
    const std::string
        m_name;  // Name of the array variable, including index notation (e.g., arr[2][1])
    void* const m_datap;  // Reference to the array variable data
    const int m_index;  // Flattened (1D) index of the array element
    const std::vector<IData> m_indices;  // Multi-dimensional indices of the array element
    const std::vector<size_t> m_idxWidths;  // Multi-dimensional indices' bit widths

    ArrayInfo(const std::string& name, void* datap, int index, const std::vector<IData>& indices,
              const std::vector<size_t>& idxWidths)
        : m_name{name}
        , m_datap{datap}
        , m_index{index}
        , m_indices{indices}
        , m_idxWidths{idxWidths} {}
};
using ArrayInfoMap = std::map<std::string, std::shared_ptr<const ArrayInfo>>;

class VlRandomVar VL_NOT_FINAL {
    std::string m_name;  // Variable name
    void* const m_datap;  // Reference to variable data
    const int m_width;  // Variable width in bits
    const int m_dimension;  //Variable dimension, default is 0
    const std::uint32_t m_randModeIdx;  // rand_mode index

public:
    VlRandomVar(const std::string& name, int width, void* datap, int dimension,
                std::uint32_t randModeIdx)
        : m_name{name}
        , m_datap{datap}
        , m_width{width}
        , m_dimension{dimension}
        , m_randModeIdx{randModeIdx} {}
    virtual ~VlRandomVar() = default;
    std::string name() const { return m_name; }
    int width() const { return m_width; }
    int dimension() const { return m_dimension; }
    virtual void* datap(int /*idx*/) const { return m_datap; }
    std::uint32_t randModeIdx() const { return m_randModeIdx; }
    bool randModeIdxNone() const { return randModeIdx() == std::numeric_limits<unsigned>::max(); }
    void set(const std::string& idx, const std::string& val) const;
    virtual void emitGetValue(std::ostream& s) const;
    virtual void emitExtract(std::ostream& s, int i) const;
    virtual void emitType(std::ostream& s) const;
    // Emit the expression referring to element j as a whole (the full var
    // for scalars, "(select arr idx...)" for array element j). Used by BSAT
    // to query/re-assert one whole element's value, not a single bit.
    virtual void emitElement(std::ostream& s, int j) const;
    // Emit the current runtime value as an SMT bit-vector literal (#b...).
    // Used by randomize(null) to pin a var to its existing value.
    virtual void emitConcreteValue(std::ostream& s) const;
    virtual int totalWidth() const;
    mutable std::shared_ptr<const ArrayInfoMap> m_arrVarsRefp;
    void setArrayInfo(const std::shared_ptr<const ArrayInfoMap>& arrVarsRefp) const {
        m_arrVarsRefp = arrVarsRefp;
    }
    mutable std::map<std::string, int> count_cache;
    void clearCountCache() const { count_cache.clear(); }
    int countMatchingElements(const ArrayInfoMap& arr_vars, const std::string& base_name) const {
        if (VL_LIKELY(count_cache.find(base_name) != count_cache.end()))
            return count_cache[base_name];
        int count = 0;
        for (int index = 0; arr_vars.find(base_name + std::to_string(index)) != arr_vars.end();
             ++index) {
            ++count;
        }
        count_cache[base_name] = count;
        return count;
    }
    bool hasMatchingElements(const ArrayInfoMap& arr_vars, const std::string& base_name) const {
        return arr_vars.find(base_name + "0") != arr_vars.end();
    }
};
// SMT key width per associative-array level (string = 128, integral = 8 * sizeof).
template <typename T>
struct VlRandomAssocKeyWidths final {
    static void push(std::vector<size_t>&) {}
};
template <typename T_Key, typename T_Value>
struct VlRandomAssocKeyWidths<VlAssocArray<T_Key, T_Value>> final {
    static void push(std::vector<size_t>& widths) {
        widths.push_back(std::is_same<T_Key, std::string>::value ? 128 : sizeof(T_Key) * 8);
        VlRandomAssocKeyWidths<T_Value>::push(widths);
    }
};
template <typename T>
class VlRandomArrayVarTemplate final : public VlRandomVar {
    // Static key widths per level for the empty-array declaration fallback
    const std::vector<size_t> m_fallbackIdxWidths;

public:
    VlRandomArrayVarTemplate(const std::string& name, int width, void* datap, int dimension,
                             std::uint32_t randModeIdx, const std::vector<size_t>& idxWidths = {})
        : VlRandomVar{name, width, datap, dimension, randModeIdx}
        , m_fallbackIdxWidths{idxWidths} {}
    void* datap(int idx) const override {
        const std::string indexed_name = name() + std::to_string(idx);
        const auto it = m_arrVarsRefp->find(indexed_name);
        if (VL_LIKELY(it != m_arrVarsRefp->end())) return it->second->m_datap;
        VL_FATAL_MT(__FILE__, __LINE__, "randomize", "indexed_name not found in m_arr_vars");
        return nullptr;  // LCOV_EXCL_BR_LINE
    }
    void emitHexs(std::ostream& s, const std::vector<IData>& indices, const size_t bit_width,
                  size_t idx) const {
        for (int j = bit_width - 4; j >= 0; j -= 4) {
            s << "0123456789abcdef"[(indices[idx] >> j) & 0xf];
        }
    }
    void emitSelect(std::ostream& s, const std::vector<IData>& indices,
                    const std::vector<size_t>& idxWidths) const {
        const size_t num_indices = idxWidths.size();
        size_t wide_size = 0;

        for (size_t idx = 0; idx < num_indices; ++idx) s << "(select ";
        s << name();

        for (size_t idx = 0; idx < num_indices; ++idx) {
            const size_t bit_width = idxWidths[idx];
            s << " #x";

            const size_t emit_count = (bit_width > 32) ? (idxWidths[idx] / 32) : 1;

            for (size_t i = 0; i < emit_count; ++i) {
                emitHexs(s, indices, (bit_width > 32) ? 32 : bit_width, wide_size + i);
            }

            wide_size += (idxWidths[idx] > 32) ? (idxWidths[idx] / 32) : 1;
            s << ")";
        }
    }
    void emitGetValue(std::ostream& s) const override {
        const int elementCounts = countMatchingElements(*m_arrVarsRefp, name());
        for (int i = 0; i < elementCounts; ++i) {
            const std::string indexed_name = name() + std::to_string(i);
            const auto it = m_arrVarsRefp->find(indexed_name);
            if (it != m_arrVarsRefp->end()) {
                const std::vector<IData>& indices = it->second->m_indices;
                const std::vector<size_t>& idxWidths = it->second->m_idxWidths;
                emitSelect(s, indices, idxWidths);
            } else {
                VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                            "indexed_name not found in m_arr_vars");
            }
        }
    }
    void emitType(std::ostream& s) const override {
        const std::string indexed_name = name() + std::to_string(0);
        const auto it = m_arrVarsRefp->find(indexed_name);
        if (it != m_arrVarsRefp->end()) {
            const std::vector<size_t>& idxWidths = it->second->m_idxWidths;
            if (dimension() > 0) {
                for (int i = 0; i < dimension(); ++i) {
                    s << "(Array (_ BitVec " << idxWidths[i] << ") ";
                }
                s << "(_ BitVec " << width() << ")";
                for (int i = 0; i < dimension(); ++i) s << ")";
            }
        } else {
            if (dimension() > 0) {
                // Empty array: declare from the static key widths, not a 32-bit default.
                for (int i = 0; i < dimension(); ++i) {
                    const size_t idxWidth = i < static_cast<int>(m_fallbackIdxWidths.size())
                                                ? m_fallbackIdxWidths[i]
                                                : 32;
                    s << "(Array (_ BitVec " << idxWidth << ") ";
                }
                s << "(_ BitVec " << width() << ")";
                for (int i = 0; i < dimension(); ++i) s << ")";
            } else {
                VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                            "indexed_name not found in m_arr_vars");
            }
        }
    }
    int totalWidth() const override {
        const int elementCounts = countMatchingElements(*m_arrVarsRefp, name());
        return width() * elementCounts;
    }
    void emitElement(std::ostream& s, int j) const override {
        const std::string indexed_name = name() + std::to_string(j);
        const auto it = m_arrVarsRefp->find(indexed_name);
        // Callers take j from totalWidth(), which counts these same keys, so the element
        // should always be there
        if (VL_UNCOVERABLE(it == m_arrVarsRefp->end())) {
            // LCOV_EXCL_START
            VL_FATAL_MT(__FILE__, __LINE__, "randomize", "indexed_name not found in m_arr_vars");
            return;
            // LCOV_EXCL_STOP
        }
        s << ' ';
        emitSelect(s, it->second->m_indices, it->second->m_idxWidths);
    }  // LCOV_EXCL_BR_LINE
    void emitExtract(std::ostream& s, int i) const override {
        const int j = i / width();
        i = i % width();
        s << " ((_ extract " << i << ' ' << i << ')';
        const std::string indexed_name = name() + std::to_string(j);
        const auto it = m_arrVarsRefp->find(indexed_name);
        if (it != m_arrVarsRefp->end()) {
            const std::vector<IData>& indices = it->second->m_indices;
            const std::vector<size_t>& idxWidths = it->second->m_idxWidths;
            emitSelect(s, indices, idxWidths);
        } else {
            VL_FATAL_MT(__FILE__, __LINE__, "randomize", "indexed_name not found in m_arr_vars");
        }
        s << ')';
    }
};

class VlSolverSession;

//=============================================================================
// Object holding constraints and variable references.
class VlRandomizer VL_NOT_FINAL {
    // MEMBERS
    std::vector<std::string> m_constraints;  // Solver-dependent hard constraints
    std::vector<std::vector<std::string>>
        m_constraintVars;  // Solver variables each hard constraint names, same order
    std::vector<std::string>
        m_constraints_line;  // fileline content of the constraint for unsat constraints
    std::vector<std::string> m_softConstraints;  // Soft constraints
    std::map<std::string, std::shared_ptr<const VlRandomVar>> m_vars;  // Solver-dependent
    std::set<std::string> m_disabledVars;  // Variables with rand_mode off (skip write-back)
                                           // variables
    ArrayInfoMap m_arr_vars;  // Tracks each element in array structures for iteration
    std::vector<std::string> m_unique_arrays;  // Arrays whose elements must be distinct
    const VlQueue<CData>* m_randmodep = nullptr;  // rand_mode state;
    const VlQueue<CData>* m_static_randmodep = nullptr;  // Static rand_mode state (shared)
    std::unordered_set<std::string> m_staticVars;  // Names of static rand vars
    int m_index = 0;  // Internal counter for key generation
    std::set<std::string> m_randcVarNames;  // Names of randc variables for cyclic tracking
    std::map<std::string, std::set<uint64_t>>
        m_randcUsedValues;  // Previously used values per randc var (exclusion-based cycling)
    size_t m_randcConstraintHash = 0;  // Hash of constraints when history was valid
    std::vector<std::pair<std::string, std::string>>
        m_solveBefore;  // Solve-before ordering pairs (beforeVar, afterVar)
    bool m_checkOnly = false;  // Set for randomize(null)
    bool isFrozenVar(const std::string& name,
                     const VlRandomVar& var) const;  // true if this var is currently frozen
    bool hasFrozenVar() const;  // true if any var is currently rand_mode(0)-frozen

    // PRIVATE METHODS
    void randomConstraint(std::ostream& os, VlRNG& rngr, int bits);
    // Fetch the model and write it into the registered variables.
    bool applyModel(VlSolverSession& sess);
    bool parseModel(std::istream& is, size_t requested);
    // Assert the maximal compatible soft-constraint set onto the open session.
    void relaxSoftConstraints(VlSolverSession& sess);
    // Indices of the "a<N>" literals named by (get-unsat-assumptions).
    std::vector<int> readUnsatAssumptions(VlSolverSession& sess);
    void reportUnsatSetup(VlSolverSession& sess, const std::vector<std::string>& uniqueExprs);
    void reportUnsatCore(VlSolverSession& sess);
    // Used-value exclusions for the randc variables this call may write,
    // skipping any whose value is already drawn and pinned
    void emitRandcExclusions(std::ostream& os,
                             const std::map<std::string, std::string>& drawn = {}) const;
    // Record the solved value of every randc variable that was not drawn
    void recordUndrawnValues(const std::map<std::string, std::string>& drawn);
    // Registered randc variables this randomize() may write
    void activeRandcVars(std::vector<std::string>& namesr) const;
    // True if every solver variable a constraint names is randc or frozen
    bool constraintIsRandcOnly(const std::vector<std::string>& varNames) const;
    // Draw the next cyclic value per randc variable, blind to rand feasibility
    // (IEEE 1800-2023 18.4.2: randc variables are solved before rand ones)
    bool drawRandcValues(VlRNG& rngr, VlSolverSession& sess,
                         const std::vector<std::string>& uniqueExprs,
                         std::map<std::string, std::string>& drawnr);
    // True if a randc value left in the cycle still admits a solution;
    // unsatr distinguishes a proven-empty tail from a solver that gave up
    bool tailFeasible(VlSolverSession& sess, const std::vector<std::string>& uniqueExprs,
                      const std::map<std::string, std::string>& drawn, bool& unsatr);
    void recordDrawnValues(const std::map<std::string, std::string>& drawn);
    size_t hashConstraints(const std::vector<std::string>& extras) const;
    bool nextRandomize(VlRNGReseeds& rngr, bool checkOnly);
    // "(distinct ...)" expression per unique-constrained array
    std::vector<std::string> buildUniqueExprs() const;
    void emitDefines(std::ostream& os) const;
    void emitDeclares(std::ostream& os, bool pinCurrent) const;
    void emitAsserts(std::ostream& os, const std::vector<std::string>& extras, bool named) const;
    bool nextFlat(VlRNG& rngr, VlSolverSession& sess, const std::vector<std::string>& uniqueExprs);

    // --- UniGen2 (a near-uniform constrained randomization sampler) fields ---
    // Implementation based on the following paper:
    // "On Parallel Scalable Uniform SAT Witness Generation", Chakraborty et al.

    using Witness = std::map<std::string, std::map<int, std::string>>;  // One sampled solution

    // Sample one random solution. False if a sample couldn't be produced
    bool unigen2(VlRNG& rngr, VlSolverSession& sess, const std::vector<std::string>& uniqueExprs);
    // Find out how finely to cut the solution space, and what cell size to accept
    bool estimateParameters(VlSolverSession& sess, VlRNG& rngr);
    // Collect up to `bound` different solutions of whatever is asserted right now.
    // diversifyRngp adds a randomization step that spreads the solutions apart
    int bsat(VlSolverSession& sess, size_t bound, std::vector<Witness>& witnesses,
             VlRNG* diversifyRngp = nullptr);
    // Add `bits` random XOR equations, which cut the solution space into cells holding
    // roughly 1/2**bits of all the solutions
    void unigenXors(std::iostream& os, VlRNG& rngr, int bits);
    // Draw a cell and refill the batch of solutions from it
    bool generateSamples(VlSolverSession& sess, VlRNG& rngr);
    // Copy one solution into the SV variables
    void writeBackWitness(const Witness& witness);

    // UniGen2: sampling state
    struct Unigen2State final {
        std::vector<Witness> loThreshWitnesses;  // Consumable batch of solutions: loThresh random
                                                 // picks out of the cell BSAT enumerated
        std::vector<std::pair<std::string, int>> bsatOrder;  // (var, element) query order
        bool isLargeSpace = false;  // Large solution space (more than 61 * 2^10 solutions)
        // Below properties are what estimateParameters worked out, kept until the constraints
        // change so the expensive search is not repeated on every call.
        bool paramsValid = false;  // Whether the values below are set
        size_t paramHash = 0;  // Constraint set they were computed for
        int hashBits = 0;  // How many XOR equations to cut the space with
        int loThresh = 0;  // Smallest usable cell, and how many samples to take
        int hiThresh = 0;  // First cell size counted as too big
        uint64_t rngReseeds = 0;  // rngr.reseeds() as of the last call
        int lastSuccessI = -1;  // Hash-bit count that worked last time, -1 if none
    };
    Unigen2State m_ug2;

    void solveDiversity(VlRNG& rngr, VlSolverSession& sess,
                        const std::map<std::string, std::string>& pinned);
    void solveDiversityPins(VlRNG& rngr, VlSolverSession& sess,
                            const std::map<std::string, std::string>& pinned);
    void solveDiversityXor(VlRNG& rngr, VlSolverSession& sess);
    // One random per-bit assumption literal per bit of the variable, numbered from npinsr
    void emitDiversityPins(std::ostream& os, VlRNG& rngr, const VlRandomVar& var,
                           int& npinsr) const;
    // Drop one conflicting assumption per round until compatible
    void solveAssumingPins(VlSolverSession& sess, int npins, bool applyToVars);
    // Layers of solve...before variables in dependency order
    bool buildSolveLayers(std::vector<std::vector<std::string>>& layersr);
    const char* phasedLogic() const;
    bool nextPhased(VlRNG& rngr, VlSolverSession& sess,
                    const std::vector<std::string>& uniqueExprs);
    bool solvePhases(VlRNG& rngr, VlSolverSession& sess,
                     const std::vector<std::vector<std::string>>& layers,
                     const std::vector<std::string>& uniqueExprs,
                     const std::map<std::string, std::string>& drawn, bool& unsatr);
    bool solvePhaseValues(VlSolverSession& sess, VlRNG& rngr,
                          const std::vector<std::string>& layerVars,
                          std::map<std::string, std::string>& solvedValuesr);
    bool readPhaseValues(VlSolverSession& sess, std::map<std::string, std::string>& solvedValuesr);
    bool parsePhaseValues(std::istream& is, std::map<std::string, std::string>& solvedValuesr);

public:
    // CONSTRUCTORS
    VlRandomizer() = default;
    ~VlRandomizer() = default;

    // METHODS
    // Finds the next solution satisfying the constraints
    bool next(VlRNGReseeds& rngr);
    // Validate the constraints against the current runtime values of every
    // registered rand variable without picking new ones.
    bool next_check_only(VlRNGReseeds& rngr);

    // ---  Process the key for associative array  ---

    // process_key: Handle integral keys (<= 32-bit)
    template <typename T_Key>
    typename std::enable_if<std::is_integral<T_Key>::value && (sizeof(T_Key) <= 4)>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        integral_index.push_back(static_cast<size_t>(key));
        indexed_name
            = base_name + "[" + std::to_string(integral_index[integral_index.size() - 1]) + "]";
        idx_width = sizeof(T_Key) * 8;
    }

    // process_key: Handle integral keys (> 32-bit), split into 2 x 32-bit segments
    template <typename T_Key>
    typename std::enable_if<std::is_integral<T_Key>::value && (sizeof(T_Key) > 4)>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        constexpr size_t segment_bits = 32;
        constexpr T_Key mask = (static_cast<T_Key>(1) << segment_bits) - 1;
        integral_index.push_back(static_cast<size_t>(key >> segment_bits));
        integral_index.push_back(static_cast<size_t>(key & mask));

        std::ostringstream hex_stream;
        hex_stream << std::hex << key;
        std::string index_string = hex_stream.str();
        index_string.erase(0, index_string.find_first_not_of('0'));
        index_string = index_string.empty() ? "0" : index_string;

        indexed_name = base_name + "[" + index_string + "]";

        idx_width = sizeof(T_Key) * 8;
    }

    // process_key: Handle wide keys (VlWide-like), segment is 32-bit per element
    template <typename T_Key>
    typename std::enable_if<VlIsVlWide<T_Key>::value>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        std::ostringstream hex_stream;
        for (size_t i = key.size(); i > 0; --i) {
            const size_t segment_value = key.at(i - 1);
            hex_stream << std::hex << segment_value;
            integral_index.push_back(segment_value);
        }
        std::string index_string = hex_stream.str();
        index_string.erase(0, index_string.find_first_not_of('0'));
        index_string = index_string.empty() ? "0" : index_string;

        indexed_name = base_name + "[" + index_string + "]";
        idx_width = key.size() * 32;
    }

    // process_key: Handle string key, encoded as 128-bit hex
    template <typename T_Key>
    typename std::enable_if<std::is_same<T_Key, std::string>::value>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        // Convert the input string to its ASCII hexadecimal representation
        std::ostringstream oss;
        for (unsigned char c : key) {
            oss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(c);
        }
        std::string hex_str = oss.str();
        // Ensure the hex string is exactly 128 bits (32 hex characters)
        hex_str = hex_str.size() > 32 ? hex_str.substr(0, 32)
                                      : std::string(32 - hex_str.size(), '0') + hex_str;

        // Split the hex string into 4 segments (32-bit per segment)
        integral_index.clear();
        for (size_t i = 0; i < hex_str.size(); i += 8) {
            integral_index.push_back(std::stoul(hex_str.substr(i, 8), nullptr, 16));
        }

        indexed_name = base_name + "["
                       + (hex_str.find_first_not_of('0') == std::string::npos
                              ? "0"
                              : hex_str.substr(hex_str.find_first_not_of('0')))
                       + "]";

        idx_width = 128;
    }

    // process_key: Unsupported key type fallback
    template <typename T_Key>
    typename std::enable_if<!std::is_integral<T_Key>::value
                            && !std::is_same<T_Key, std::string>::value
                            && !VlIsVlWide<T_Key>::value>::type
    process_key(const T_Key& key, std::string& indexed_name, std::vector<size_t>& integral_index,
                const std::string& base_name, size_t& idx_width) {
        VL_FATAL_MT(__FILE__, __LINE__, "randomize",
                    "Unsupported: Only integral and string index of associative array is "
                    "supported currently.");
    }

    // Mark a variable as rand_mode-disabled: solver keeps it in m_vars
    // (so constraints still reference it) but skips write-back after solving.
    void set_var_disabled(const char* name) { m_disabledVars.insert(name); }
    // Clear disabled state for a variable
    void clear_var_disabled(const char* name) { m_disabledVars.erase(name); }

    // ---  write_var to register variables  ---
    // Register scalar variable (non-struct, basic type)
    template <typename T>
    typename std::enable_if<!VlContainsCustomStruct<T>::value && !IsVlUnpacked<T>::value,
                            void>::type
    write_var(T& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) != m_vars.end()) return;
        // TODO: make_unique once VlRandomizer is per-instance not per-ref
        m_vars[name]
            = std::make_shared<const VlRandomVar>(name, width, &var, dimension, randmodeIdx);
    }

    // Register user-defined struct variable by recursively writing members
    template <typename T>
    typename std::enable_if<VlIsCustomStruct<T>::value, void>::type
    write_var(T& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        modifyMembers(var, var.memberIndices(), name);
    }

    // Register queue of non-struct types
    template <typename T, size_t N_MaxSize>
    typename std::enable_if<!VlContainsCustomStruct<T>::value, void>::type
    write_var(VlQueue<T, N_MaxSize>& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) == m_vars.end()) {
            m_vars[name] = std::make_shared<const VlRandomArrayVarTemplate<VlQueue<T, N_MaxSize>>>(
                name, width, &var, dimension, randmodeIdx);
        }
        if (dimension > 0) {
            m_index = 0;
            clear_arr_table(name);
            record_arr_table(var, name, dimension, {}, {});
            m_vars[name]->clearCountCache();
        }
    }

    // Register queue of structs
    template <typename T, size_t N_MaxSize>
    typename std::enable_if<VlContainsCustomStruct<T>::value, void>::type
    write_var(VlQueue<T, N_MaxSize>& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (dimension > 0) record_struct_arr(var, name, dimension, {}, {});
    }
    // Register unpacked array of non-struct types
    template <typename T, std::size_t N_Depth>
    typename std::enable_if<!VlContainsCustomStruct<T>::value, void>::type
    write_var(VlUnpacked<T, N_Depth>& var, uint32_t width, const std::string& name,
              uint32_t dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) == m_vars.end()) {
            m_vars[name]
                = std::make_shared<const VlRandomArrayVarTemplate<VlUnpacked<T, N_Depth>>>(
                    name, width, &var, dimension, randmodeIdx);
        }

        if (dimension > 0) {
            m_index = 0;
            clear_arr_table(name);
            record_arr_table(var, name, dimension, {}, {});
            m_vars[name]->clearCountCache();
        }
    }
    // Register unpacked array of structs
    template <typename T, std::size_t N_Depth>
    typename std::enable_if<VlContainsCustomStruct<T>::value, void>::type
    write_var(VlUnpacked<T, N_Depth>& var, int /*width*/, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (dimension > 0) record_struct_arr(var, name, dimension, {}, {});
    }

    // Register associative array of non-struct types
    template <typename T_Key, typename T_Value>
    typename std::enable_if<!VlContainsCustomStruct<T_Value>::value, void>::type
    write_var(VlAssocArray<T_Key, T_Value>& var, int width, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (m_vars.find(name) == m_vars.end()) {
            std::vector<size_t> keyWidths;
            VlRandomAssocKeyWidths<VlAssocArray<T_Key, T_Value>>::push(keyWidths);
            m_vars[name]
                = std::make_shared<const VlRandomArrayVarTemplate<VlAssocArray<T_Key, T_Value>>>(
                    name, width, &var, dimension, randmodeIdx, keyWidths);
        }
        if (dimension > 0) {
            m_index = 0;
            clear_arr_table(name);
            record_arr_table(var, name, dimension, {}, {});
            m_vars[name]->clearCountCache();
        }
    }

    // Register associative array of structs
    template <typename T_Key, typename T_Value>
    typename std::enable_if<VlContainsCustomStruct<T_Value>::value, void>::type
    write_var(VlAssocArray<T_Key, T_Value>& var, int /*width*/, const char* name, int dimension,
              std::uint32_t randmodeIdx = std::numeric_limits<std::uint32_t>::max()) {
        if (dimension > 0) record_struct_arr(var, name, dimension, {}, {});
    }

    // ---  Record Arrays: flat and struct  ---

    // Record a flat (non-class) element into the array variable table
    template <typename T>
    typename std::enable_if<!std::is_class<T>::value || VlIsVlWide<T>::value, void>::type
    record_arr_table(T& var, const std::string& name, int /*dimension*/,
                     std::vector<IData> indices, std::vector<size_t> idxWidths) {
        const std::string key = generateKey(name, m_index);
        m_arr_vars[key] = std::make_shared<ArrayInfo>(name, &var, m_index, indices, idxWidths);
        ++m_index;
    }

    // This is the "Sender" API for the generated code.
    // The elements to make distinct are taken from the array element table at
    // solve time, so a container resized by the solver is handled correctly.
    void rand_unique(const std::string& name) { m_unique_arrays.push_back(name); }

    // Recursively record all elements in an unpacked array
    template <typename T, std::size_t N_Depth>
    void record_arr_table(VlUnpacked<T, N_Depth>& var, const std::string& name, int dimension,
                          std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (N_Depth != 0)) {
            idxWidths.push_back(32);
            for (size_t i = 0; i < N_Depth; ++i) {
                const std::string indexed_name = name + "[" + std::to_string(i) + "]";
                indices.push_back(i);
                record_arr_table(var.operator[](i), indexed_name, dimension - 1, indices,
                                 idxWidths);
                indices.pop_back();
            }
        }
    }

    // Recursively record all elements in a queue
    template <typename T, size_t N_MaxSize>
    void record_arr_table(VlQueue<T, N_MaxSize>& var, const std::string& name, int dimension,
                          std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (var.size() != 0)) {
            idxWidths.push_back(32);
            for (size_t i = 0; i < var.size(); ++i) {
                const std::string indexed_name = name + "[" + std::to_string(i) + "]";
                indices.push_back(i);
                record_arr_table(var.atWrite(i), indexed_name, dimension - 1, indices, idxWidths);
                indices.pop_back();
            }
        }
    }

    // Recursively record all elements in an associative array
    template <typename T_Key, typename T_Value>
    void record_arr_table(VlAssocArray<T_Key, T_Value>& var, const std::string& name,
                          int dimension, std::vector<IData> indices,
                          std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (var.size() != 0)) {
            for (auto it = var.begin(); it != var.end(); ++it) {
                const T_Key& key = it->first;
                const T_Value& value = it->second;

                std::string indexed_name;
                std::vector<size_t> integral_index;
                size_t idx_width = 0;

                process_key(key, indexed_name, integral_index, name, idx_width);

                // Update indices and widths
                idxWidths.push_back(idx_width);
                indices.insert(indices.end(), integral_index.begin(), integral_index.end());

                record_arr_table(var.atWrite(key), indexed_name, dimension - 1, indices,
                                 idxWidths);

                // Cleanup indices and widths
                idxWidths.pop_back();
                indices.resize(indices.size() - integral_index.size());
            }
        }
    }

    // Register a single structArray element via write_var
    template <typename T>
    typename std::enable_if<VlContainsCustomStruct<T>::value, void>::type
    record_struct_arr(T& var, const std::string& name, int /*dimension*/,
                      std::vector<IData> indices, std::vector<size_t> idxWidths) {
        std::ostringstream oss;
        for (size_t i = 0; i < indices.size(); ++i) {
            oss << std::hex << std::setw(int(idxWidths[i] / 4)) << std::setfill('0')
                << static_cast<int>(indices[i]);
            if (i < indices.size() - 1) oss << ".";
        }
        write_var(var, 1ULL,
                  oss.str().length() > 0 ? (name + "." + oss.str()).c_str() : name.c_str(), 1ULL);
    }

    // Recursively process VlUnpacked of structs
    template <typename T, std::size_t N_Depth>
    void record_struct_arr(VlUnpacked<T, N_Depth>& var, const std::string& name, int dimension,
                           std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if (dimension > 0 && N_Depth != 0) {
            constexpr size_t idx_width = 1 << VL_CLOG2_CE_Q(VL_CLOG2_CE_Q(N_Depth) + 1);
            idxWidths.push_back(idx_width);
            for (size_t i = 0; i < N_Depth; ++i) {
                indices.push_back(i);
                record_struct_arr(var.operator[](i), name, dimension - 1, indices, idxWidths);
                indices.pop_back();
            }
        }
    }

    // Recursively process VlQueue of structs
    template <typename T, size_t N_MaxSize>
    void record_struct_arr(VlQueue<T, N_MaxSize>& var, const std::string& name, int dimension,
                           std::vector<IData> indices, std::vector<size_t> idxWidths) {
        if ((dimension > 0) && (var.size() != 0)) {
            idxWidths.push_back(32);
            for (size_t i = 0; i < var.size(); ++i) {
                indices.push_back(i);
                record_struct_arr(var.atWrite(i), name, dimension - 1, indices, idxWidths);
                indices.pop_back();
            }
        }
    }

    // Recursively process associative arrays of structs
    template <typename T_Key, typename T_Value>
    void record_struct_arr(VlAssocArray<T_Key, T_Value>& var, const std::string& name,
                           int dimension, const std::vector<IData>& indices,
                           const std::vector<size_t>& idxWidths) {
        if ((dimension > 0) && (!var.empty())) {
            for (auto it = var.begin(); it != var.end(); ++it) {
                const T_Key& key = it->first;
                const T_Value& value = it->second;

                std::string indexed_name;
                std::vector<size_t> integral_index;
                size_t idx_width = 0;

                process_key(key, indexed_name, integral_index, name, idx_width);
                std::ostringstream oss;
                for (int i = 0; i < integral_index.size(); ++i)
                    oss << std::hex << static_cast<int>(integral_index[i]);

                std::string result = oss.str();
                result.insert(result.begin(), int(idx_width / 4) - result.size(), '0');
                record_struct_arr(var.atWrite(key), name + "." + result, dimension - 1, indices,
                                  idxWidths);
            }
        }
    }

    // ---  Helper functions  ---

    // Helper: Register all members of a user-defined struct
    template <typename T, std::size_t... I>
    void modifyMembers(T& obj, std::index_sequence<I...>, const std::string& baseName) {
        // Use the indices to access each member via std::get
        (void)std::initializer_list<int>{
            (write_var(std::get<I>(obj.getMembers(obj)), obj.memberWidth()[I],
                       (baseName + "." + obj.memberNames()[I]).c_str(), obj.memberDimension()[I]),
             0)...};
    }

    // Helper: Generate unique variable key from name and index
    static std::string generateKey(const std::string& name, int idx) {
        if (!name.empty() && name[0] == '\\') {
            const size_t space_pos = name.find(' ');
            return (space_pos != std::string::npos ? name.substr(0, space_pos) : name)
                   + std::to_string(idx);
        }
        const size_t bracket_pos = name.find('[');
        return (bracket_pos != std::string::npos ? name.substr(0, bracket_pos) : name)
               + std::to_string(idx);
    }

    // Helper: Clear existing array element entries for a base name
    void clear_arr_table(const std::string& name) {
        for (int index = 0;; ++index) {
            const std::string key = generateKey(name, index);
            const auto it = m_arr_vars.find(key);
            if (it == m_arr_vars.end()) break;
            m_arr_vars.erase(it);
        }
    }

    void hard(std::string&& constraint, std::initializer_list<const char*> varNames = {},
              const char* filename = "", uint32_t linenum = 0, const char* source = "");
    void soft(std::string&& constraint, const char* filename = "", uint32_t linenum = 0,
              const char* source = "");
    void pin_var(const char* name, int width, uint64_t value) {
        std::string constraint = "(__Vbv (= "s + name + " (_ bv" + std::to_string(value) + " "
                                 + std::to_string(width) + ")))";
        hard(std::move(constraint), {name});
    }
    void disable_soft(const std::string& varName);
    void clearConstraints();
    void clearAll();  // Clear both constraints and variables
    void markRandc(const char* name);  // Mark variable as randc for cyclic tracking
    void solveBefore(const std::string& beforeName,
                     const std::string& afterName);  // Register solve-before ordering
    void set_randmode(const VlQueue<CData>& randmode) { m_randmodep = &randmode; }
    // Shared across all instances; consulted instead of m_randmodep for vars marked via
    // mark_var_static().
    void set_static_randmode(const VlQueue<CData>& randmode) { m_static_randmodep = &randmode; }
    void mark_var_static(const char* const name) { m_staticVars.insert(name); }
#ifdef VL_DEBUG
    void dump() const;
#endif
};

//=============================================================================

// Light wrapper for RNG used by std::randomize() to support scope-level randomization.
class VlStdRandomizer final : public VlRandomizer {
    // MEMBERS
    VlRNGReseeds m_rng;  // Random number generator

public:
    // CONSTRUCTORS
    VlStdRandomizer() = default;
    ~VlStdRandomizer() = default;

private:
    // Wide type specialization (>64 bits)
    template <typename T>
    typename std::enable_if<VlIsVlWide<T>::value, bool>::type
    basicStdRandomizationImpl(T& value, size_t width) {
        VL_RANDOM_RNG_W(m_rng, width, value);
        // Mask off garbage bits in last word
        const int words = VL_WORDS_I(width);
        const int bitsInLastWord = width & VL_SIZEBITS_I;
        if (bitsInLastWord) value.at(words - 1) &= VL_MASK_I(bitsInLastWord);
        return true;
    }

    // Scalar type specialization (<=64 bits)
    template <typename T>
    typename std::enable_if<!VlIsVlWide<T>::value, bool>::type
    basicStdRandomizationImpl(T& value, size_t width) {
        if (width <= 32) {
            value = VL_MASK_I(width) & VL_RANDOM_RNG_I(m_rng);
        } else {
            value = VL_MASK_Q(width) & VL_RANDOM_RNG_Q(m_rng);
        }
        return true;
    }

public:
    // Scalar/wide randomization
    template <typename T>
    bool basicStdRandomization(T& value, size_t width) {
        return basicStdRandomizationImpl(value, width);
    }

    // Unpacked array randomization
    template <typename T_Unpacked, std::size_t N_Depth>
    bool basicStdRandomization(VlUnpacked<T_Unpacked, N_Depth>& value, size_t width) {
        for (size_t i = 0; i < N_Depth; ++i) { basicStdRandomization(value.operator[](i), width); }
        return true;
    }

    // Queue/dynamic array randomization
    template <typename T_Value, size_t N_MaxSize>
    bool basicStdRandomization(VlQueue<T_Value, N_MaxSize>& value, size_t width) {
        for (int i = 0; i < value.size(); ++i) { basicStdRandomization(value.atWrite(i), width); }
        return true;
    }

    // Associative array randomization
    template <typename T_Key, typename T_Value>
    bool basicStdRandomization(VlAssocArray<T_Key, T_Value>& value, size_t width) {
        T_Key key;
        for (int exists = value.first(key); exists; exists = value.next(key)) {
            basicStdRandomization(value.atWrite(key), width);
        }
        return true;
    }
    bool next() { return VlRandomizer::next(m_rng); }
};

//======================================================================
//Helper method for dynamic array handling in SMT expressions

inline std::string vlToSolverHex(const IData& value) {
    std::ostringstream oss;
    oss << std::hex << std::setfill('0') << std::setw(8) << value;
    return oss.str();
}

#endif  // Guard
