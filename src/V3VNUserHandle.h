// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Utility to hang advanced data structures of
// AstNode::user*p() pointers with automatic memory management.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3VNUSERHANDLE_H_
#define VERILATOR_V3VNUSERHANDLE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <type_traits>
#include <utility>
#include <vector>

//============================================================================
// VNAux is juts a type pair, to be passed to VNUser*Handle as type parameter
//============================================================================

template <typename T_Node, typename T_Data>
struct VNAux final {
    static_assert(std::is_base_of<AstNode, T_Node>::value, "T_Node must be an AstNode type");
    using Node = T_Node;
    using Data = T_Data;
};

//============================================================================
// Simple accessors for the 4 user fields
//============================================================================

class VNUser1Accessor final {
public:
    static VNUser& user(AstNode* nodep) { return nodep->m_user1u; }
    static VNUser user(const AstNode* nodep) { return nodep->m_user1u; }
    static uint32_t& nodeGeneration(AstNode* nodep) { return nodep->m_user1Cnt; }
    static uint32_t nodeGeneration(const AstNode* nodep) { return nodep->m_user1Cnt; }
    static uint32_t currentGeneration() { return VNUser1InUse::s_userCntGbl; }
};

class VNUser2Accessor final {
public:
    static VNUser& user(AstNode* nodep) { return nodep->m_user2u; }
    static VNUser user(const AstNode* nodep) { return nodep->m_user2u; }
    static uint32_t& nodeGeneration(AstNode* nodep) { return nodep->m_user2Cnt; }
    static uint32_t nodeGeneration(const AstNode* nodep) { return nodep->m_user2Cnt; }
    static uint32_t currentGeneration() { return VNUser2InUse::s_userCntGbl; }
};

class VNUser3Accessor final {
public:
    static VNUser& user(AstNode* nodep) { return nodep->m_user3u; }
    static VNUser user(const AstNode* nodep) { return nodep->m_user3u; }
    static uint32_t& nodeGeneration(AstNode* nodep) { return nodep->m_user3Cnt; }
    static uint32_t nodeGeneration(const AstNode* nodep) { return nodep->m_user3Cnt; }
    static uint32_t currentGeneration() { return VNUser3InUse::s_userCntGbl; }
};

class VNUser4Accessor final {
public:
    static VNUser& user(AstNode* nodep) { return nodep->m_user4u; }
    static VNUser user(const AstNode* nodep) { return nodep->m_user4u; }
    static uint32_t& nodeGeneration(AstNode* nodep) { return nodep->m_user4Cnt; }
    static uint32_t nodeGeneration(const AstNode* nodep) { return nodep->m_user4Cnt; }
    static uint32_t currentGeneration() { return VNUser4InUse::s_userCntGbl; }
};

//============================================================================
// Implementation of access to the user data for one node type (Aux::Node)
//============================================================================

// There are 2 implementation flavours: Data held directly vs indirectly
template <typename Accessor, typename Aux, bool Indirect>
class VNUserHandleImpl;

// Implementation for Data held directly
template <typename Accessor, typename Aux>
class VNUserHandleImpl<Accessor, Aux, /* Indirect: */ false> VL_NOT_FINAL {
    using Node = typename Aux::Node;
    using Data = typename Aux::Data;
    static_assert(sizeof(Data) <= sizeof(VNUser), "'Data' does not fit directly");

protected:
    VNUserHandleImpl() = default;
    ~VNUserHandleImpl() = default;
    VL_UNCOPYABLE(VNUserHandleImpl);

public:
    // Get a reference to the user data. If not current, construct it with given arguments.
    template <typename... Args>
    Data& operator()(Node* nodep, Args&&... args) {
        Data* const storagep = reinterpret_cast<Data*>(&Accessor::user(nodep));
        if (Accessor::nodeGeneration(nodep) != Accessor::currentGeneration()) {
            Accessor::nodeGeneration(nodep) = Accessor::currentGeneration();
            new (storagep) Data{std::forward<Args>(args)...};
        }
        return *storagep;
    }

    // Get a reference to the user data. The node is const, so it must be current.
    Data& operator()(const Node* nodep) {
        UASSERT_OBJ(Accessor::nodeGeneration(nodep) == Accessor::currentGeneration(), nodep,
                    "User data is stale on const AstNode");
        return *Accessor::user(nodep).template to<Data*>();
    }
};

// Implementation for Data held indirectly
template <typename Accessor, typename Aux>
class VNUserHandleImpl<Accessor, Aux, /* Indirect: */ true> VL_NOT_FINAL {
    using Node = typename Aux::Node;
    using Data = typename Aux::Data;
    static_assert(sizeof(Data) > sizeof(VNUser), "'Data' should fit directly");

    std::deque<Data> m_allocated;

protected:
    VNUserHandleImpl() = default;
    ~VNUserHandleImpl() = default;
    VL_UNCOPYABLE(VNUserHandleImpl);

public:
    // Get a reference to the user data. If not current, construct it with given arguments.
    template <typename... Args>
    Data& operator()(Node* nodep, Args&&... args) {
        if (Accessor::nodeGeneration(nodep) != Accessor::currentGeneration()) {
            Accessor::nodeGeneration(nodep) = Accessor::currentGeneration();
            m_allocated.emplace_back(std::forward<Args>(args)...);
            Accessor::user(nodep) = VNUser{&m_allocated.back()};
        }
        return *Accessor::user(nodep).template to<Data*>();
    }

    // Get a reference to the user data. The node is const, so it must be current.
    Data& operator()(const Node* nodep) {
        UASSERT_OBJ(Accessor::nodeGeneration(nodep) == Accessor::currentGeneration(), nodep,
                    "User data is stale on const AstNode");
        return *Accessor::user(nodep).template to<Data*>();
    }
};

//============================================================================
// This is a variadic 'unroller' template that eventually derives from
// VNUserHandleImpl for each VNAux parameter passed to it
//============================================================================

// Generic template
template <typename Accessor, typename AuxFirst, typename... AuxRest>
class VNUserHandleTemplate;

// Specialization for two or more Aux arguments
template <typename Accessor, typename Aux1, typename Aux2, typename... AuxRest>
class VNUserHandleTemplate<Accessor, Aux1, Aux2, AuxRest...> VL_NOT_FINAL
    : public VNUserHandleTemplate<Accessor, Aux1>,  // Single argument version
      public VNUserHandleTemplate<Accessor, Aux2, AuxRest...>  // Generic version
{
public:
    using VNUserHandleTemplate<Accessor, Aux1>::operator();
    using VNUserHandleTemplate<Accessor, Aux2, AuxRest...>::operator();
};

// Specialization for one Aux argument - just derives from the implementation
template <typename Accessor, typename Aux>
class VNUserHandleTemplate<Accessor, Aux> VL_NOT_FINAL
    : public VNUserHandleImpl<Accessor, Aux, (sizeof(typename Aux::Data) > sizeof(VNUser))> {
    static_assert(std::is_same<Aux, VNAux<typename Aux::Node, typename Aux::Data>>::value,
                  "Don't invent your own 'VNAux'!");
};

//============================================================================
// The actual AstNode 'user' data handlers, to be used in client code
//============================================================================

template <typename... T_VNAuxs>
class VNUser1Handle final : public VNUserHandleTemplate<VNUser1Accessor, T_VNAuxs...> {
    const VNUser1InUse m_user1InUse;
};
template <typename... T_VNAuxs>
class VNUser2Handle final : public VNUserHandleTemplate<VNUser2Accessor, T_VNAuxs...> {
    const VNUser2InUse m_user2InUse;
};
template <typename... T_VNAuxs>
class VNUser3Handle final : public VNUserHandleTemplate<VNUser3Accessor, T_VNAuxs...> {
    const VNUser3InUse m_user3InUse;
};
template <typename... T_VNAuxs>
class VNUser4Handle final : public VNUserHandleTemplate<VNUser4Accessor, T_VNAuxs...> {
    const VNUser4InUse m_user4InUse;
};

#endif  // Guard
