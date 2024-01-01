// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Utility to hang advanced data structures of
// AstNode::user*p() pointers with automatic memory management.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ASTUSERALLOCATOR_H_
#define VERILATOR_V3ASTUSERALLOCATOR_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <type_traits>
#include <utility>
#include <vector>

template <class T_Node, class T_Data, int T_UserN>
class AstUserAllocatorBase VL_NOT_FINAL {
    static_assert(1 <= T_UserN && T_UserN <= 4, "Wrong user pointer number");
    static_assert(std::is_base_of<AstNode, T_Node>::value, "T_Node must be an AstNode type");

private:
    std::deque<T_Data> m_allocated;

    T_Data* getUserp(const T_Node* nodep) const {
        if VL_CONSTEXPR_CXX17 (T_UserN == 1) {
            const VNUser user = nodep->user1u();
            return user.to<T_Data*>();
        } else if VL_CONSTEXPR_CXX17 (T_UserN == 2) {
            const VNUser user = nodep->user2u();
            return user.to<T_Data*>();
        } else if VL_CONSTEXPR_CXX17 (T_UserN == 3) {
            const VNUser user = nodep->user3u();
            return user.to<T_Data*>();
        } else {
            const VNUser user = nodep->user4u();
            return user.to<T_Data*>();
        }
    }

    void setUserp(T_Node* nodep, T_Data* userp) const {
        if VL_CONSTEXPR_CXX17 (T_UserN == 1) {
            nodep->user1u(VNUser{userp});
        } else if VL_CONSTEXPR_CXX17 (T_UserN == 2) {
            nodep->user2u(VNUser{userp});
        } else if VL_CONSTEXPR_CXX17 (T_UserN == 3) {
            nodep->user3u(VNUser{userp});
        } else {
            nodep->user4u(VNUser{userp});
        }
    }

protected:
    AstUserAllocatorBase() {
        if VL_CONSTEXPR_CXX17 (T_UserN == 1) {
            VNUser1InUse::check();
        } else if VL_CONSTEXPR_CXX17 (T_UserN == 2) {
            VNUser2InUse::check();
        } else if VL_CONSTEXPR_CXX17 (T_UserN == 3) {
            VNUser3InUse::check();
        } else {
            VNUser4InUse::check();
        }
    }

    VL_UNCOPYABLE(AstUserAllocatorBase);

public:
    // Get a reference to the user data. If does not exist, construct it with given arguments.
    template <typename... Args>
    T_Data& operator()(T_Node* nodep, Args&&... args) {
        T_Data* userp = getUserp(nodep);
        if (!userp) {
            m_allocated.emplace_back(std::forward<Args>(args)...);
            userp = &m_allocated.back();
            setUserp(nodep, userp);
        }
        return *userp;
    }

    // Get a reference to the user data
    T_Data& operator()(const T_Node* nodep) const {
        T_Data* const userp = getUserp(nodep);
        UASSERT_OBJ(userp, nodep, "Missing User data on const AstNode");
        return *userp;
    }

    // Get a pointer to the user data if exists, otherwise nullptr
    T_Data* tryGet(const T_Node* nodep) { return getUserp(nodep); }

    void clear() { m_allocated.clear(); }
};

// User pointer allocator classes. T_Node is the type of node the allocator should be applied to
// and is there for a bit of extra type safety. T_Data is the type of the data structure
// managed by the allocator.
template <class T_Node, class T_Data>
class AstUser1Allocator final : public AstUserAllocatorBase<T_Node, T_Data, 1> {};
template <class T_Node, class T_Data>
class AstUser2Allocator final : public AstUserAllocatorBase<T_Node, T_Data, 2> {};
template <class T_Node, class T_Data>
class AstUser3Allocator final : public AstUserAllocatorBase<T_Node, T_Data, 3> {};
template <class T_Node, class T_Data>
class AstUser4Allocator final : public AstUserAllocatorBase<T_Node, T_Data, 4> {};

#endif  // Guard
