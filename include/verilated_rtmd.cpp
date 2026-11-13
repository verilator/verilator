// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
//
// Verilated run time model descriptor (RTMD) implementation code
//
//=========================================================================

#include "verilated_config.h"
#include "verilatedos.h"

#include "verilated_rtmd.h"

#include <ostream>

//=========================================================================
// VlRtmdDataType

uint32_t VlRtmdDataType::elements() const {
    const int32_t l = left();
    const int32_t r = right();
    return static_cast<uint32_t>(l > r ? l - r : r - l) + 1;
}

uint32_t VlRtmdDataType::width() const {
    const VlRtmdDataTypeRow& type = row();
    if (const VlRtmdDataTypeRow::Atom* const atomp = type.atomp()) {  //
        return atomp->m_bits;
    }
    if (type.enump()) return enumBase().width();
    if (type.packedArrayp()) return elements() * elemType().width();
    if (const VlRtmdDataTypeRow::PackedStruct* const strctp = type.packedStructp()) {
        uint32_t bits = 0;
        for (uint32_t i = 0; i < strctp->m_count; ++i) { bits += memberType(i).width(); }
        return bits;
    }
    if (const VlRtmdDataTypeRow::PackedUnion* const unionp = type.packedUnionp()) {
        uint32_t bits = 0;
        for (uint32_t i = 0; i < unionp->m_count; ++i) {
            const uint32_t memberBits = memberType(i).width();
            if (memberBits > bits) bits = memberBits;
        }
        return bits;
    }
    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "", "VlRtmdDataType::width called on a non packed type");
    return 0;
    // LCOV_EXCL_STOP
}

int32_t VlRtmdDataType::left() const {
    if (const VlRtmdDataTypeRow::PackedArray* const arrayp = row().packedArrayp()) {
        return arrayp->m_left;
    }
    if (const VlRtmdDataTypeRow::UnpackedArray* const arrayp = row().unpackedArrayp()) {
        return arrayp->m_left;
    }
    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "", "VlRtmdDataType::left called on a non array type");
    return 0;
    // LCOV_EXCL_STOP
}

int32_t VlRtmdDataType::right() const {
    if (const VlRtmdDataTypeRow::PackedArray* const arrayp = row().packedArrayp()) {
        return arrayp->m_right;
    }
    if (const VlRtmdDataTypeRow::UnpackedArray* const arrayp = row().unpackedArrayp()) {
        return arrayp->m_right;
    }
    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "", "VlRtmdDataType::right called on a non array type");
    return 0;
    // LCOV_EXCL_STOP
}

uint32_t VlRtmdDataType::memberCount() const {
    if (const VlRtmdDataTypeRow::PackedStruct* const structp = row().packedStructp()) {
        return structp->m_count;
    }
    if (const VlRtmdDataTypeRow::PackedUnion* const unionp = row().packedUnionp()) {
        return unionp->m_count;
    }
    if (const VlRtmdDataTypeRow::UnpackedStruct* const structp = row().unpackedStructp()) {
        return structp->m_count;
    }
    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "", "VlRtmdDataType::memberCount called on a non struct type");
    return 0;
    // LCOV_EXCL_STOP
}

VlRtmdDataType::AtomKind VlRtmdDataType::atomKind() const {
    if (const VlRtmdDataTypeRow::Atom* const atomp = row().atomp()) return atomp->m_kind;
    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "", "VlRtmdDataType::atomKind called on a non atom type");
    return AtomKind::LOGIC;
    // LCOV_EXCL_STOP
}

VlRtmdDataType::StorageKind VlRtmdDataType::storageKind() const {
    // Events and reals are stored by their own type
    if (isAtom()) {
        const AtomKind kind = atomKind();
        if (kind == AtomKind::EVENT) return StorageKind::EVENT;
        if (kind == AtomKind::DOUBLE) return StorageKind::DOUBLE;
    }
    // Everything else by its width
    return storageKind(width());
}

VlRtmdDataType::StorageKind VlRtmdDataType::storageKind(uint32_t bits) {
    if (bits <= VL_BYTESIZE) return StorageKind::CDATA;
    if (bits <= VL_SHORTSIZE) return StorageKind::SDATA;
    if (bits <= VL_IDATASIZE) return StorageKind::IDATA;
    if (bits <= VL_QUADSIZE) return StorageKind::QDATA;
    return StorageKind::WDATA;
}

const char* VlRtmdDataType::atomKeyword(bool& signedByDefault) const {
    assert(row().atomp());
    signedByDefault = false;
    switch (row().atomp()->m_kind) {
    case VlRtmdDataTypeRow::Atom::Kind::DOUBLE: signedByDefault = true; return "real";
    case VlRtmdDataTypeRow::Atom::Kind::BIT: return "bit";
    case VlRtmdDataTypeRow::Atom::Kind::LOGIC: return "logic";
    case VlRtmdDataTypeRow::Atom::Kind::CHANDLE: return "chandle";
    case VlRtmdDataTypeRow::Atom::Kind::EVENT: return "event";
    case VlRtmdDataTypeRow::Atom::Kind::TIME: return "time";
    case VlRtmdDataTypeRow::Atom::Kind::INTEGER: signedByDefault = true; return "integer";
    case VlRtmdDataTypeRow::Atom::Kind::INT: signedByDefault = true; return "int";
    case VlRtmdDataTypeRow::Atom::Kind::SHORTINT: signedByDefault = true; return "shortint";
    case VlRtmdDataTypeRow::Atom::Kind::LONGINT: signedByDefault = true; return "longint";
    case VlRtmdDataTypeRow::Atom::Kind::BYTE: signedByDefault = true; return "byte";
    }
    return "?";  // LCOV_EXCL_LINE
}

std::string VlRtmdDataType::toString() const {
    // A range as '[left:right]'
    const auto range = [](int32_t left, int32_t right) {
        return '[' + std::to_string(left) + ':' + std::to_string(right) + ']';
    };

    // An unpacked array is its element type, followed by the unpacked dimensions after '_'
    if (row().unpackedArrayp()) {
        std::string dims;
        VlRtmdDataType elem = *this;
        while (const VlRtmdDataTypeRow::UnpackedArray* const arrayp
               = elem.row().unpackedArrayp()) {
            dims += range(arrayp->m_left, arrayp->m_right);
            elem = elem.elemType();
        }
        return elem.toString() + " _ " + dims;
    }
    // A struct or union is shown by its keywords only, not its members
    if (row().unpackedStructp()) return "struct";

    // A packed type is its base type, followed by the packed dimensions. The signedness is that
    // of the outermost type.
    std::string dims;
    const VlRtmdDataTypeRow::PackedArray* const outerArrayp = row().packedArrayp();
    VlRtmdDataType elem = *this;
    while (const VlRtmdDataTypeRow::PackedArray* const arrayp = elem.row().packedArrayp()) {
        dims += range(arrayp->m_left, arrayp->m_right);
        elem = elem.elemType();
    }
    std::string str;
    bool isSigned = false;
    bool signedByDefault = false;
    if (const VlRtmdDataTypeRow::Atom* const atomp = elem.row().atomp()) {
        str = elem.atomKeyword(signedByDefault);
        isSigned = atomp->m_signed;
        // A vector of bits
        if (atomp->m_kind == VlRtmdDataTypeRow::Atom::Kind::BIT
            || atomp->m_kind == VlRtmdDataTypeRow::Atom::Kind::LOGIC) {
            if (atomp->m_bits > 1) dims += range(static_cast<int32_t>(atomp->m_bits) - 1, 0);
        }
    } else if (elem.row().enump()) {
        // An enum is shown by its base type
        str = "enum " + elem.enumBase().toString();
    } else if (const VlRtmdDataTypeRow::PackedStruct* const structp = elem.row().packedStructp()) {
        str = "struct packed";
        isSigned = structp->m_signed;
    } else if (const VlRtmdDataTypeRow::PackedUnion* const unionp = elem.row().packedUnionp()) {
        str = "union packed";
        isSigned = unionp->m_signed;
    }
    if (outerArrayp) isSigned = outerArrayp->m_signed;
    if (isSigned != signedByDefault) str += isSigned ? " signed" : " unsigned";
    if (!dims.empty()) str += ' ' + dims;
    return str;
}

//=========================================================================
// VlRtmdHierListener::Path

std::string VlRtmdHierListener::Path::name() const {
    std::string name = m_rootp->hierName();
    for (const Entry& entry : m_entries) {
        const VlRtmdHierRow* const rowp = entry.first;
        // The root and root IO levels of a model are not part of the name
        if (const VlRtmdHierRow::Push* const pushp = rowp->pushp()) {
            if (pushp->m_kind == VlRtmdHierRow::Push::Kind::ROOT) continue;
            if (pushp->m_kind == VlRtmdHierRow::Push::Kind::ROOTIO) continue;
        }
        if (!name.empty()) name += '.';  // Root name might be empty
        if (const VlRtmdHierRow::Instance* const instancep = rowp->instancep()) {
            name += instancep->m_namep;
        } else if (const VlRtmdHierRow::IfaceRef* const ifaceRefp = rowp->ifaceRefp()) {
            name += ifaceRefp->m_namep;
        } else if (const VlRtmdHierRow::Partition* const partitionp = rowp->partitionp()) {
            name += partitionp->m_namep;
        } else {
            name += entry.second->m_namep;
        }
    }
    return name;
}

//=========================================================================
// VlRtmdHierListener

void VlRtmdHierListener::walkContext(const VerilatedContext& context) {
    m_models = context.models();
    // Enumerate all models under the context, in hierarchical name-sorted-order.
    // This way a model comes before the partitions it instantiates, which have
    // its name as a prefix. So a partition is walked through the PARTITION row of
    // its parent before it is reached in this loop. Any models not walked as a
    // partition under a previous one are then roots.
    for (const std::pair<const std::string, VerilatedModel*>& pair : m_models) {
        walkModel(*pair.second, nullptr);
    }
    m_walked.clear();
    m_models.clear();
}

void VlRtmdHierListener::walkModel(const VerilatedModel& model,
                                   const VlRtmdHierRow* partitionRowp) {
    // Skip if walked already, as a partition of a previous model
    if (!m_walked.insert(&model).second) return;

    const VlRtmd* const rtmdp = model.rtmd();
    // A model without descriptors yields nothing
    if (!rtmdp) return;

    uint32_t startIdx = 0;
    if (!partitionRowp) {
        // A root model starts the path, and is walked from its root level.
        m_path.root(model);
    } else {
        // A partition continues the path, so is walked from within its root level,
        // which is not part of the path. Its ROOTIO level is skipped, if it exists.
        assert(rtmdp->hierRow(startIdx).pushp()->m_kind == VlRtmdHierRow::Push::Kind::ROOT);
        ++startIdx;
        const VlRtmdHierRow::Push* const pushp = rtmdp->hierRow(startIdx).pushp();
        if (pushp && pushp->m_kind == VlRtmdHierRow::Push::Kind::ROOTIO) {
            // Holds no levels
            while (!rtmdp->hierRow(++startIdx).popp()) assert(!rtmdp->hierRow(startIdx).pushp());
            ++startIdx;
        }
    }
    const size_t startDepth = m_path.size();
    walkRows(model, partitionRowp, startIdx);
    assert(m_path.size() == startDepth);  // Every Push must have a Pop
}

void VlRtmdHierListener::walkRows(const VerilatedModel& model, const VlRtmdHierRow* partitionRowp,
                                  uint32_t rowIdx) {
    const VlRtmd* const rtmdp = model.rtmd();
    // The number of levels open on entry, the last of which ends this walk
    const size_t startDepth = m_path.size();
    // The Instance row before the current Push, if any
    const VlRtmdHierRow* instanceRowp = nullptr;
    for (;; ++rowIdx) {
        const VlRtmdHierRow* const rowp = &rtmdp->hierRow(rowIdx);
        // The Instance row is attached to the Push following it
        if (rowp->instancep()) {
            assert(!instanceRowp);
            instanceRowp = rowp;
            continue;
        }

        if (const VlRtmdHierRow::Push* const pushp = rowp->pushp()) {
            // In the root level of a partition's model, which is not part of the path
            const bool inPartitionRoot = partitionRowp && m_path.size() == startDepth;
            // This push is the partition module instance (first MODULE level under the partition)
            const bool isPartitionTop
                = inPartitionRoot && pushp->m_kind == VlRtmdHierRow::Push::Kind::MODULE;
            // The Instance of an instance level Push
            const VlRtmdHierRow::Instance* const instancep
                = instanceRowp ? instanceRowp->instancep() : nullptr;
            // The row naming this level in the path
            const VlRtmdHierRow* const namingRowp = isPartitionTop ? partitionRowp
                                                    : instanceRowp ? instanceRowp
                                                                   : rowp;
            instanceRowp = nullptr;
            // The level is in the path while entered
            m_path.push(namingRowp, pushp);

            // Within a skipped level, only track the path, to find its Pop
            if (m_skipDepth) continue;

            // Whether the listener should descend, based on return value of enter methods
            bool enter = true;
            switch (pushp->m_kind) {
            case VlRtmdHierRow::Push::Kind::ROOT:
                assert(!partitionRowp);  // Skipped by walkModel for partitions
                enter = enterRoot(model);
                break;
            case VlRtmdHierRow::Push::Kind::ROOTIO:
                assert(!partitionRowp);  // Skipped by walkModel for partitions
                enter = enterScope(ScopeKind::ROOTIO, pushp->m_namep, pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::MODULE: {
                const char* const namep = isPartitionTop ? partitionRowp->partitionp()->m_namep  //
                                                         : instancep->m_namep;
                enter = enterInstance(InstanceKind::MODULE, namep, pushp->m_namep, pushp->m_flags);
                break;
            }
            case VlRtmdHierRow::Push::Kind::INTERFACE:
                enter = enterInstance(InstanceKind::INTERFACE, instancep->m_namep, pushp->m_namep,
                                      pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::PACKAGE:
                // Omit packages in a partition's model. The hierarchical implementation
                // currently duplicates packages into each model, and the state of these copies
                // is not traced.
                enter = !inPartitionRoot
                        && enterInstance(InstanceKind::PACKAGE, instancep->m_namep, pushp->m_namep,
                                         pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::FUNCTION:
                enter = enterScope(ScopeKind::FUNCTION, pushp->m_namep, pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::TASK:
                enter = enterScope(ScopeKind::TASK, pushp->m_namep, pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::GENERATE:
                enter = enterScope(ScopeKind::GENERATE, pushp->m_namep, pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::BEGIN:
                enter = enterScope(ScopeKind::BEGIN, pushp->m_namep, pushp->m_flags);
                break;
            case VlRtmdHierRow::Push::Kind::FORK:
                enter = enterScope(ScopeKind::FORK, pushp->m_namep, pushp->m_flags);
                break;
            }
            // Skip the contents of this level, up to its Pop
            if (!enter) m_skipDepth = m_path.size();
            continue;
        }
        assert(!instanceRowp);  // Must have been followed by a Push

        if (rowp->popp()) {
            // The Pop of the level open on entry ends this walk
            if (m_path.size() == startDepth) return;
            // The level being closed, in the path until exited
            const VlRtmdHierRow* const namingRowp = m_path.back().first;
            const VlRtmdHierRow::Push* const pushp = m_path.back().second;
            const VlRtmdHierRow::Push::Kind kind = pushp->m_kind;
            // The name of an instance level, as passed to 'enterInstance'
            const auto instanceNamep = [namingRowp]() {
                if (const VlRtmdHierRow::Instance* const ip = namingRowp->instancep()) {
                    return ip->m_namep;
                }
                return namingRowp->partitionp()->m_namep;  // The top instance of a partition
            };
            if (m_skipDepth) {
                // Closing the skipped level ends the skip. exit* is not called.
                if (m_path.size() == m_skipDepth) m_skipDepth = 0;
            } else {
                switch (kind) {
                case VlRtmdHierRow::Push::Kind::ROOT:  //
                    exitRoot(model);
                    break;
                case VlRtmdHierRow::Push::Kind::ROOTIO:
                    exitScope(ScopeKind::ROOTIO, pushp->m_namep, pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::MODULE:
                    exitInstance(InstanceKind::MODULE, instanceNamep(), pushp->m_namep,
                                 pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::INTERFACE:
                    exitInstance(InstanceKind::INTERFACE, instanceNamep(), pushp->m_namep,
                                 pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::PACKAGE:
                    exitInstance(InstanceKind::PACKAGE, instanceNamep(), pushp->m_namep,
                                 pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::FUNCTION:
                    exitScope(ScopeKind::FUNCTION, pushp->m_namep, pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::TASK:
                    exitScope(ScopeKind::TASK, pushp->m_namep, pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::GENERATE:
                    exitScope(ScopeKind::GENERATE, pushp->m_namep, pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::BEGIN:
                    exitScope(ScopeKind::BEGIN, pushp->m_namep, pushp->m_flags);
                    break;
                case VlRtmdHierRow::Push::Kind::FORK:
                    exitScope(ScopeKind::FORK, pushp->m_namep, pushp->m_flags);
                    break;
                }
            }
            m_path.pop();
            // The Pop of the root level of a root model is the last row of the table
            if (kind == VlRtmdHierRow::Push::Kind::ROOT) return;
            continue;
        }

        if (const VlRtmdHierRow::Partition* const partp = rowp->partitionp()) {
            // The partition model is registered, under its hierarchical path (its %m)
            const auto it = m_models.find(m_path.name() + '.' + partp->m_namep);
            assert(it != m_models.end());
            walkModel(*it->second, rowp);
            continue;
        }

        // Rest need not be visited when skipping
        if (m_skipDepth) continue;

        if (const VlRtmdHierRow::IfaceRef* const irp = rowp->ifaceRefp()) {
            // Walk the descriptors of the referenced interface in place, under the reference
            const VlRtmdHierRow* const ifacePushRowp = &rtmdp->hierRow(irp->m_pushIdx);
            m_path.push(rowp, ifacePushRowp->pushp());
            if (enterIfaceRef(irp->m_namep, ifacePushRowp->pushp()->m_namep,
                              ifacePushRowp->pushp()->m_flags)) {
                walkRows(model, partitionRowp, irp->m_pushIdx + 1);
                exitIfaceRef(irp->m_namep, ifacePushRowp->pushp()->m_namep,
                             ifacePushRowp->pushp()->m_flags);
            }
            m_path.pop();
            continue;
        }

        if (const VlRtmdHierRow::Var* const sp = rowp->varp()) {
            const VlRtmdVarType varType = rtmdp->varType(sp->m_typeIdx);
            const VlRtmdDataType dtype = varType.dataType();
            const uint8_t* const datap = static_cast<const uint8_t*>(rtmdp->varAddress(*rowp));
            const VlRtmdActSet actSet = rtmdp->actSet(sp->m_actSetIdx);
            if (onVar(sp->m_namep, varType, dtype, actSet, datap, sp->m_flags)) {
                walkDtype(sp->m_namep, varType, dtype, actSet, datap, NOLSB);
            }
            continue;
        }

        VL_FATAL_MT(__FILE__, __LINE__, "", "Unhandled hierarchy row");
    }
}

void VlRtmdHierListener::walkDtype(const char* namep, const VlRtmdVarType& varType,
                                   const VlRtmdDataType& dtype, const VlRtmdActSet& actSet,
                                   const uint8_t* datap, const uint32_t lsb) {
    // An array is its elements, in declaration order
    if (dtype.isUnpackedArray() || dtype.isPackedArray()) {
        const bool isPacked = dtype.isPackedArray();
        if (isPacked) {
            enterPackedArray(namep, dtype);
        } else {
            enterUnpackedArray(namep, dtype);
        }
        const VlRtmdDataType elemType = dtype.elemType();
        const int32_t left = dtype.left();
        const int32_t right = dtype.right();
        const int32_t step = left <= right ? 1 : -1;
        for (uint32_t i = 0; i < dtype.elements(); ++i) {
            const int32_t index = left + static_cast<int32_t>(i) * step;
            const std::string name = '[' + std::to_string(index) + ']';
            const uint8_t* elemp = datap;
            uint32_t elemLsb = lsb;
            if (isPacked) {
                // A packed array element is a bit slice, with the 'right' element at the LSB.
                const int32_t position = index > right ? index - right : right - index;
                elemLsb = (lsb == NOLSB ? 0 : lsb)
                          + static_cast<uint32_t>(position) * elemType.width();
            } else if (datap) {
                // An unpacked array element has an address of its own. Elements are stored by
                // index from the lower bound, whatever the direction of the range.
                const int32_t position = index - std::min(left, right);
                elemp += static_cast<uint32_t>(position) * dtype.elemBytes();
            }
            if (onComponent(name.c_str(), varType, elemType, actSet, elemp, elemLsb)) {
                walkDtype(name.c_str(), varType, elemType, actSet, elemp, elemLsb);
            }
        }
        if (isPacked) {
            exitPackedArray(namep, dtype);
        } else {
            exitUnpackedArray(namep, dtype);
        }
        return;
    }

    // A struct or union is its members
    if (dtype.isUnpackedStruct() || dtype.isPackedStruct() || dtype.isPackedUnion()) {
        if (dtype.isPackedStruct()) {
            enterPackedStruct(namep, dtype);
        } else if (dtype.isPackedUnion()) {
            enterPackedUnion(namep, dtype);
        } else {
            enterUnpackedStruct(namep, dtype);
        }
        const bool isPacked = !dtype.isUnpackedStruct();
        for (uint32_t i = 0; i < dtype.memberCount(); ++i) {
            const VlRtmdDataTypeRow::Member& member = dtype.member(i);
            const VlRtmdDataType memberType = dtype.memberType(i);
            // A packed member is a bit slice at the offset of its LSB. An unpacked member has an
            // address of its own.
            const uint8_t* memberp = datap;
            uint32_t memberLsb = lsb;
            if (isPacked) {
                memberLsb = (lsb == NOLSB ? 0 : lsb) + member.m_offset;
            } else if (datap) {
                memberp += member.m_offset;
            }
            if (onComponent(member.m_namep, varType, memberType, actSet, memberp, memberLsb)) {
                walkDtype(member.m_namep, varType, memberType, actSet, memberp, memberLsb);
            }
        }
        if (dtype.isPackedStruct()) {
            exitPackedStruct(namep, dtype);
        } else if (dtype.isPackedUnion()) {
            exitPackedUnion(namep, dtype);
        } else {
            exitUnpackedStruct(namep, dtype);
        }
        return;
    }

    // LCOV_EXCL_START
    VL_FATAL_MT(__FILE__, __LINE__, "",
                "VlRtmdHierListener::walkDtype called on a non compound data type");
    // LCOV_EXCL_STOP
}

//=============================================================================
// Debug dump

// Prints the hierarchy enumerated by the walker, one line per level and variable, see hierDump
class VlRtmdHierDumper final : public VlRtmdHierListener {
    std::ostream& m_os;  // Where to write
    const bool m_components;  // Walk the components of arrays, structs and unions
    int m_indent = 0;  // Current indentation level

    void line(const std::string& text) const {
        m_os << std::string(2 * m_indent, ' ') << text << '\n';
    }
    bool open(const std::string& text, bool hasVars) {
        line(text + (hasVars ? "" : " (no variables)"));
        ++m_indent;
        return true;
    }
    void close(const std::string& text) {
        --m_indent;
        line(text);
    }
    // Print a value, and walk the parts of unpacked arrays and structs
    bool value(const std::string& name, const VlRtmdDataType& dtype, const void* datap) {
        line(name + " : " + dtype.toString() + (datap ? "" : " (no address)"));
        if (!m_components) return false;
        // Packed arrays of single bits, e.g. 'logic [7:0]', are not split, as too many
        if (dtype.isPackedArray()) return dtype.elemType().width() > 1;
        return dtype.isUnpackedArray() || dtype.isUnpackedStruct() || dtype.isPackedStruct()
               || dtype.isPackedUnion();
    }

    static std::string kindName(VlRtmdVarType::Kind kind) {
        switch (kind) {
        case VlRtmdVarType::Kind::VAR: return "var"s;
        case VlRtmdVarType::Kind::WIRE: return "wire"s;
        case VlRtmdVarType::Kind::WREAL: return "wreal"s;
        case VlRtmdVarType::Kind::TRI: return "tri"s;
        case VlRtmdVarType::Kind::TRI0: return "tri0"s;
        case VlRtmdVarType::Kind::TRI1: return "tri1"s;
        case VlRtmdVarType::Kind::TRIAND: return "triand"s;
        case VlRtmdVarType::Kind::TRIOR: return "trior"s;
        case VlRtmdVarType::Kind::SUPPLY0: return "supply0"s;
        case VlRtmdVarType::Kind::SUPPLY1: return "supply1"s;
        case VlRtmdVarType::Kind::GPARAM: return "parameter"s;
        case VlRtmdVarType::Kind::LPARAM: return "localparam"s;
        case VlRtmdVarType::Kind::SPECPARAM: return "specparam"s;
        case VlRtmdVarType::Kind::GENVAR: return "genvar"s;
        }
        return "?"s;
    }
    static std::string directionName(VlRtmdVarType::Direction direction) {
        switch (direction) {
        case VlRtmdVarType::Direction::NONE: return ""s;
        case VlRtmdVarType::Direction::INPUT: return "input "s;
        case VlRtmdVarType::Direction::OUTPUT: return "output "s;
        case VlRtmdVarType::Direction::INOUT: return "inout "s;
        case VlRtmdVarType::Direction::REF: return "ref "s;
        case VlRtmdVarType::Direction::CONSTREF: return "const ref "s;
        }
        return "?"s;
    }
    static std::string instanceName(InstanceKind kind) {
        switch (kind) {
        case InstanceKind::MODULE: return "module"s;
        case InstanceKind::INTERFACE: return "interface"s;
        case InstanceKind::PACKAGE: return "package"s;
        }
        return "?"s;
    }
    static std::string scopeEnd(ScopeKind kind) {
        switch (kind) {
        case ScopeKind::ROOTIO: return "endrootio"s;
        case ScopeKind::FUNCTION: return "endfunction"s;
        case ScopeKind::TASK: return "endtask"s;
        case ScopeKind::GENERATE: return "endgenerate"s;
        case ScopeKind::BEGIN: return "end"s;
        case ScopeKind::FORK: return "join"s;
        }
        return "?"s;
    }
    static std::string scopeName(ScopeKind kind) {
        switch (kind) {
        case ScopeKind::ROOTIO: return "rootio"s;
        case ScopeKind::FUNCTION: return "function"s;
        case ScopeKind::TASK: return "task"s;
        case ScopeKind::GENERATE: return "generate"s;
        case ScopeKind::BEGIN: return "begin"s;
        case ScopeKind::FORK: return "fork"s;
        }
        return "?"s;
    }

    bool enterRoot(const VerilatedModel& model) override {
        line("# Generated by VlRtmd::hierDump");
        return open(model.hierName() + " : $root"s, true);
    }
    void exitRoot(const VerilatedModel& model) override {
        close("end$root : "s + model.hierName());
    }
    bool enterInstance(InstanceKind kind, const char* namep, const char* modNamep,
                       HierFlags flags) override {
        return open(namep + " : "s + instanceName(kind) + " " + modNamep, flags.hasVars());
    }
    void exitInstance(InstanceKind kind, const char* namep, const char*, HierFlags) override {
        close("end" + instanceName(kind) + " : " + namep);
    }
    bool enterIfaceRef(const char* namep, const char* modNamep, HierFlags flags) override {
        return open(namep + " : interface reference "s + modNamep, flags.hasVars());
    }
    void exitIfaceRef(const char* namep, const char*, HierFlags) override {
        close("endinterface reference : "s + namep);
    }
    bool enterScope(ScopeKind kind, const char* namep, HierFlags flags) override {
        return open(namep + " : "s + scopeName(kind), flags.hasVars());
    }
    void exitScope(ScopeKind kind, const char* namep, HierFlags) override {
        close(scopeEnd(kind) + " : " + namep);
    }
    bool onVar(const char* namep, const VlRtmdVarType& varType, const VlRtmdDataType& dtype,
               const VlRtmdActSet&, const void* datap, VarFlags) override {
        return value(directionName(varType.direction()) + kindName(varType.kind()) + " " + namep,
                     dtype, datap);
    }
    void enterUnpackedArray(const char*, const VlRtmdDataType& dtype) override {
        open("enterUnpackedArray ["s + std::to_string(dtype.left()) + ":"
                 + std::to_string(dtype.right()) + "]",
             true);
    }
    void exitUnpackedArray(const char*, const VlRtmdDataType&) override {
        close("exitUnpackedArray");
    }
    void enterUnpackedStruct(const char*, const VlRtmdDataType& dtype) override {
        open("enterUnpackedStruct, "s + std::to_string(dtype.memberCount()) + " members", true);
    }
    void exitUnpackedStruct(const char*, const VlRtmdDataType&) override {
        close("exitUnpackedStruct");
    }
    void enterPackedArray(const char*, const VlRtmdDataType& dtype) override {
        open("enterPackedArray ["s + std::to_string(dtype.left()) + ":"
                 + std::to_string(dtype.right()) + "]",
             true);
    }
    void exitPackedArray(const char*, const VlRtmdDataType&) override { close("exitPackedArray"); }
    void enterPackedStruct(const char*, const VlRtmdDataType& dtype) override {
        open("enterPackedStruct, "s + std::to_string(dtype.memberCount()) + " members", true);
    }
    void exitPackedStruct(const char*, const VlRtmdDataType&) override {
        close("exitPackedStruct");
    }
    void enterPackedUnion(const char*, const VlRtmdDataType& dtype) override {
        open("enterPackedUnion, "s + std::to_string(dtype.memberCount()) + " members", true);
    }
    void exitPackedUnion(const char*, const VlRtmdDataType&) override { close("exitPackedUnion"); }
    bool onComponent(const char* namep, const VlRtmdVarType&, const VlRtmdDataType& dtype,
                     const VlRtmdActSet&, const void* datap, uint32_t lsb) override {
        // A component of a packed value is located by its bit offset
        return value(namep + (lsb != NOLSB ? " @" + std::to_string(lsb) : ""s), dtype, datap);
    }

public:
    VlRtmdHierDumper(std::ostream& os, const VerilatedContext& context, bool components)
        : m_os{os}
        , m_components{components} {
        walkContext(context);
    }
};

void VlRtmd::hierDump(std::ostream& os, const VerilatedContext& context, bool components) {
    VlRtmdHierDumper{os, context, components};
}
