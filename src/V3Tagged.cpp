// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Transform tagged union constructs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Tagged's Transformations:
//
// Transform tagged union constructs into low-level bit operations:
//
// 1. AstTaggedExpr (tagged MemberName expr):
//    -> Combine tag bits with member value:
//       (tag_value << max_member_width) | (value & data_mask)
//
// 2. Case matches:
//    case (v) matches
//      tagged Invalid: stmt1
//      tagged Valid .n: stmt2
//    endcase
//    ->
//    { type_of_n n;
//      switch(VL_SEL(v, tag_lsb, tag_width)) {
//        case 0: stmt1; break;
//        case 1: n = VL_SEL(v, 0, member_width); stmt2; break;
//      }
//    }
//
// 3. If matches:
//    if (e matches tagged Valid .n) body
//    ->
//    { type_of_n n;
//      if (VL_SEL(e, tag_lsb, tag_width) == tag_value) {
//        n = VL_SEL(e, 0, member_width);
//        body
//      }
//    }
//
// 4. Member access on tagged union (v.MemberName):
//    -> Extract the data portion (runtime tag check would be added for safety)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Tagged.h"

#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Tagged visitor

class TaggedVisitor final : public VNVisitor {
    // STATE
    VDouble0 m_statTaggedExprs;  // Statistic tracking
    VDouble0 m_statTaggedMatches;  // Statistic tracking

    // Cache for O(1) union member lookups
    std::unordered_map<AstUnionDType*, std::unordered_map<string, AstMemberDType*>>
        m_unionMemberCache;  // Union member cache

    // Cache for O(1) struct/union member lookups (for path traversal)
    std::unordered_map<AstNodeUOrStructDType*, std::unordered_map<string, AstMemberDType*>>
        m_structMemberCache;

    // Context structs to reduce argument counts

    // Context for tagged matching operations
    struct TaggedMatchContext VL_NOT_FINAL {
        FileLine* fl;
        AstUnionDType* unionp;
        AstMemberDType* memberp;
        bool isUnpacked;
    };

    // Context for case matches processing
    struct CaseMatchContext VL_NOT_FINAL {
        FileLine* fl;
        AstUnionDType* unionp;
        AstVar* tempVarp;
        bool isUnpacked;
        int tagWidth;
    };

    // Parts for building if statement body
    struct IfBodyParts VL_NOT_FINAL {
        AstVar* varDeclp;
        AstVar* origVarp;  // Original pattern variable for O(1) pointer comparison
        AstNode* varAssignsp;
        AstNodeExpr* guardp;
    };

    // METHODS

    // Check if name ends with suffix - O(1) string comparison
    static bool hasSuffix(const string& name, const string& suffix) {
        return name.size() > suffix.size()
               && name.compare(name.size() - suffix.size(), suffix.size(), suffix) == 0;
    }

    // Get or build union member map for O(1) lookups
    std::unordered_map<string, AstMemberDType*>& getUnionMemberMap(AstUnionDType* unionp) {
        auto it = m_unionMemberCache.find(unionp);
        if (it != m_unionMemberCache.end()) return it->second;
        auto& map = m_unionMemberCache[unionp];
        for (AstMemberDType* mp = unionp->membersp(); mp; mp = VN_AS(mp->nextp(), MemberDType)) {
            map[mp->name()] = mp;
        }
        return map;
    }

    // Find a member in the tagged union by name - O(1) with cache
    // V3Width validates member exists before V3Tagged runs, so result is always non-null
    AstMemberDType* findMember(AstUnionDType* unionp, const string& name) {
        auto& map = getUnionMemberMap(unionp);
        auto it = map.find(name);
        UASSERT_OBJ(it != map.end(), unionp, "Member '" << name << "' not found in tagged union");
        return it->second;
    }

    // Check if a dtype is void
    bool isVoidDType(AstNodeDType* dtp) {
        dtp = dtp->skipRefp();
        return VN_IS(dtp, BasicDType)
               && VN_AS(dtp, BasicDType)->keyword() == VBasicDTypeKwd::CVOID;
    }

    // Find the pattern variable from a VarRef in the given tree
    // Searches for a VarRef whose variable name ends with __DOT__ + varName
    // O(N) where N = number of VarRefs; uses short-circuit evaluation after first match
    AstVar* findPatternVarFromBody(AstNode* nodep, const string& varName) {
        if (!nodep) return nullptr;
        const string suffix = "__DOT__" + varName;
        AstVar* foundVarp = nullptr;
        nodep->foreach([&](AstVarRef* varRefp) {
            if (!foundVarp && hasSuffix(varRefp->varp()->name(), suffix)) {
                foundVarp = varRefp->varp();
            }
        });
        return foundVarp;
    }

    // Replace all references to pattern variable with the new local variable
    // Uses O(1) pointer comparison when origVarp is provided
    void replacePatternVarRefs(AstNode* nodep, AstVar* origVarp, AstVar* newVarp) {
        nodep->foreach([&](AstVarRef* varRefp) {
            if (varRefp->varp() == origVarp) {
                varRefp->varp(newVarp);
                varRefp->name(newVarp->name());
            }
        });
    }

    // String-based overload for case matches where pattern variables are in a begin block
    // V3Begin renames all pattern variables with __DOT__ prefix, so we search for the suffix
    void replacePatternVarRefs(AstNode* nodep, const string& patternVarName, AstVar* newVarp) {
        const string suffix = "__DOT__" + patternVarName;
        nodep->foreachAndNext([&](AstVarRef* varRefp) {
            if (hasSuffix(varRefp->varp()->name(), suffix)) {
                varRefp->varp(newVarp);
                varRefp->name(newVarp->name());
            }
        });
    }

    // Walk up AST to find containing assignment. O(D) where D = AST depth.
    // Returns nullptr if no assignment found before statement boundary (valid - triggers
    // UNSUPPORTED)
    static AstAssign* findContainingAssign(AstNode* nodep) {
        for (AstNode* p = nodep->backp(); p; p = p->backp()) {
            if (AstAssign* const a = VN_CAST(p, Assign)) return a;
            if (VN_IS(p, NodeStmt)) return nullptr;
        }
        return nullptr;
    }

    // Check if node is under an assignment (not direct RHS). O(D) where D = AST depth.
    static bool isUnderAssignment(AstNode* nodep) {
        for (AstNode* p = nodep->backp(); p; p = p->backp()) {
            if (VN_IS(p, Assign)) return true;
            if (VN_IS(p, NodeStmt)) return false;
        }
        return false;
    }

    // Create a constant with the given value and width
    AstConst* makeConst(FileLine* fl, int value, int width) {
        return new AstConst{fl, AstConst::WidthedValue{}, width, static_cast<uint32_t>(value)};
    }

    // Create a bit selection: VL_SEL_I(data, lsb, width) -> data[lsb +: width]
    AstNodeExpr* makeSel(FileLine* fl, AstNodeExpr* fromp, int lsb, int width) {
        return new AstSel{fl, fromp, lsb, width};
    }

    // Create tag extraction from a packed tagged union value
    AstNodeExpr* makeTagExtract(FileLine* fl, AstNodeExpr* valuep, AstUnionDType* unionp) {
        const int tagLsb = unionp->maxMemberWidth();
        const int tagWidth = unionp->tagBitWidth();
        return makeSel(fl, valuep, tagLsb, tagWidth);
    }

    // Create data extraction from a packed tagged union value
    AstNodeExpr* makeDataExtract(FileLine* fl, AstNodeExpr* valuep, AstUnionDType* unionp,
                                 int memberWidth) {
        return makeSel(fl, valuep, 0, memberWidth);
    }

    // Create tag extraction from an unpacked tagged union value (struct field access)
    AstNodeExpr* makeTagExtractUnpacked(FileLine* fl, AstNodeExpr* valuep) {
        AstStructSel* const selp = new AstStructSel{fl, valuep, "__Vtag"};
        selp->dtypeSetBitSized(32, VSigning::UNSIGNED);
        return selp;
    }

    // Create data extraction from an unpacked tagged union value (struct field access)
    AstNodeExpr* makeDataExtractUnpacked(FileLine* fl, AstNodeExpr* valuep,
                                         const string& memberName, AstNodeDType* memberDtp) {
        AstStructSel* const selp = new AstStructSel{fl, valuep, memberName};
        selp->dtypep(memberDtp);
        return selp;
    }

    // Transform: tagged MemberName [expr]
    // Into: (tag << max_member_width) | (expr & ((1 << member_width) - 1))
    AstNodeExpr* transformTaggedExpr(AstTaggedExpr* nodep, AstUnionDType* unionp) {
        FileLine* const fl = nodep->fileline();
        AstMemberDType* const memberp = findMember(unionp, nodep->name());
        // memberp validity checked by V3Width before V3Tagged runs

        const int tagIndex = memberp->tagIndex();
        const int maxMemberWidth = unionp->maxMemberWidth();
        const int totalWidth = unionp->taggedTotalWidth();

        // Create the tag value positioned at MSB
        // tag_value << max_member_width
        // Packed unions must have at least one non-void member for meaningful bit representation
        UASSERT_OBJ(maxMemberWidth > 0, nodep, "Packed union must have non-void members");
        AstNodeExpr* tagValp = makeConst(fl, tagIndex, totalWidth);
        tagValp = new AstShiftL{fl, tagValp, makeConst(fl, maxMemberWidth, 32)};
        tagValp->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);

        // Handle member value
        const bool isVoid = isVoidDType(memberp->subDTypep());
        if (isVoid) {
            // Void member - just return tag value
            tagValp->dtypep(unionp);
            return tagValp;
        }

        // Get member expression and extend/truncate to maxMemberWidth
        AstNodeExpr* valuep = nodep->exprp()->unlinkFrBack();
        const int memberWidth = memberp->width();

        // Extend value to maxMemberWidth if needed
        if (memberWidth < maxMemberWidth) {
            valuep = new AstExtend{fl, valuep, maxMemberWidth};
            valuep->dtypeSetBitSized(maxMemberWidth, VSigning::UNSIGNED);
        }
        // Note: memberWidth > maxMemberWidth is impossible since maxMemberWidth
        // is computed as std::max() of all member widths

        // Extend value to total width for OR operation
        // totalWidth = maxMemberWidth + tagWidth, and tagWidth >= 1, so always need extend
        valuep = new AstExtend{fl, valuep, totalWidth};
        valuep->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);

        // Combine: tag | value
        AstNodeExpr* const resultp = new AstOr{fl, tagValp, valuep};
        resultp->dtypep(unionp);

        return resultp;
    }

    // Get tagged union type from matches expression
    AstUnionDType* getMatchesUnionType(AstMatches* matchesp) {
        AstNode* const patternp = matchesp->patternp();
        const bool isTaggedPattern = VN_IS(patternp, TaggedPattern);
        const bool isTaggedExpr = VN_IS(patternp, TaggedExpr);
        UASSERT_OBJ(isTaggedPattern || isTaggedExpr, matchesp,
                    "Pattern must be TaggedPattern or TaggedExpr");
        UASSERT_OBJ(patternp->dtypep(), matchesp, "V3Width ensures dtypep is set");
        return VN_CAST(patternp->dtypep()->skipRefp(), UnionDType);
    }

    // Create tag comparison expression
    AstNodeExpr* createTagComparison(FileLine* fl, AstNodeExpr* exprp, AstUnionDType* unionp,
                                     int tagIndex, bool isUnpacked) {
        AstNodeExpr* const exprClonep = exprp->cloneTree(false);
        AstNodeExpr* tagExtractp;
        AstNodeExpr* tagConstp;
        if (isUnpacked) {
            tagExtractp = makeTagExtractUnpacked(fl, exprClonep);
            tagConstp = makeConst(fl, tagIndex, 32);
        } else {
            tagExtractp = makeTagExtract(fl, exprClonep, unionp);
            tagConstp = makeConst(fl, tagIndex, unionp->tagBitWidth());
        }
        AstNodeExpr* const condp = new AstEq{fl, tagExtractp, tagConstp};
        condp->dtypeSetBit();
        return condp;
    }

    // Info for a pattern variable in nested pattern (struct or array)
    struct PatVarInfo VL_NOT_FINAL {
        string name;  // Pattern variable name
        string accessPath;  // Access path: "field" for struct, "[0]" for array, "field[0].x" mixed
        AstNodeDType* dtypep;  // Type from V3Width
    };

    // Info for a nested tag check (for nested tagged patterns like "tagged Value .y")
    struct NestedTagCheck VL_NOT_FINAL {
        string accessPath;  // Access path to the union (e.g., "maybe" for o.Data.maybe)
        int tagIndex;  // Tag index to match
    };

    // Collect pattern variables from array pattern. O(N).
    void collectArrayPatternVars(AstPattern* patp, AstNodeDType* elemDtp, const string& basePath,
                                 std::vector<PatVarInfo>& out) {
        size_t idx = 0;
        for (AstPatMember* itemp = VN_CAST(patp->itemsp(), PatMember); itemp;
             itemp = VN_CAST(itemp->nextp(), PatMember), ++idx) {
            if (AstPatternVar* const pvp = VN_CAST(itemp->lhssp(), PatternVar)) {
                const string path = basePath + "[" + std::to_string(idx) + "]";
                out.push_back({pvp->name(), path, elemDtp});
            }
        }
    }

    // Recursively collect pattern variables from nested struct pattern. O(N).
    // basePath is the current access path prefix (empty at top level)
    // Handles Pattern, PatternVar, TaggedPattern (for nested tagged union patterns)
    // Also collects tag checks for nested tagged patterns when tagChecks is provided
    void collectNestedPatternVars(AstNode* nodep, AstNodeDType* baseDtp, const string& basePath,
                                  std::vector<PatVarInfo>& out,
                                  std::vector<NestedTagCheck>* tagChecks = nullptr) {
        // Simple pattern variable
        if (AstPatternVar* const pvp = VN_CAST(nodep, PatternVar)) {
            out.push_back({pvp->name(), basePath, pvp->dtypep()});
            return;
        }

        // Handle TaggedPattern (e.g., "tagged Value .y" inside struct pattern)
        // The tagged union member name becomes part of the access path
        // Also generates a tag check for this nested tagged pattern
        if (AstTaggedPattern* const tagPatp = VN_CAST(nodep, TaggedPattern)) {
            AstUnionDType* const unionDtp = VN_CAST(baseDtp->skipRefp(), UnionDType);
            if (unionDtp) {
                AstMemberDType* const memberp = findMember(unionDtp, tagPatp->name());
                // Add tag check for this nested tagged pattern
                if (tagChecks) tagChecks->push_back({basePath, memberp->tagIndex()});
                const string memberPath
                    = basePath.empty() ? tagPatp->name() : basePath + "." + tagPatp->name();
                if (tagPatp->patternp()) {
                    collectNestedPatternVars(tagPatp->patternp(), memberp->subDTypep(), memberPath,
                                             out, tagChecks);
                }
            }
            return;
        }

        // Handle TaggedExpr used as pattern (same structure as TaggedPattern)
        if (AstTaggedExpr* const tagExprp = VN_CAST(nodep, TaggedExpr)) {
            AstUnionDType* const unionDtp = VN_CAST(baseDtp->skipRefp(), UnionDType);
            if (unionDtp) {
                AstMemberDType* const memberp = findMember(unionDtp, tagExprp->name());
                // Add tag check for this nested tagged pattern
                if (tagChecks) tagChecks->push_back({basePath, memberp->tagIndex()});
                const string memberPath
                    = basePath.empty() ? tagExprp->name() : basePath + "." + tagExprp->name();
                if (tagExprp->exprp()) {
                    collectNestedPatternVars(tagExprp->exprp(), memberp->subDTypep(), memberPath,
                                             out, tagChecks);
                }
            }
            return;
        }

        AstPattern* const patp = VN_CAST(nodep, Pattern);
        if (!patp) return;
        // Check if it's an array or struct type
        AstNodeDType* const skipDtp = baseDtp->skipRefp();
        if (AstUnpackArrayDType* const arrayDtp = VN_CAST(skipDtp, UnpackArrayDType)) {
            collectArrayPatternVars(patp, arrayDtp->subDTypep(), basePath, out);
            return;
        }
        AstNodeUOrStructDType* const structDtp = VN_CAST(skipDtp, NodeUOrStructDType);
        UASSERT_OBJ(structDtp, nodep, "V3Width sets struct/array dtype on patterns");
        // Build member name->dtype map for lookup
        std::map<string, std::pair<string, AstNodeDType*>> memberInfo;
        size_t posIdx = 0;
        for (AstMemberDType* memp = structDtp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType), ++posIdx) {
            memberInfo[memp->name()] = {memp->name(), memp->subDTypep()};
        }
        // Iterate pattern members
        posIdx = 0;
        std::vector<AstMemberDType*> memberList;
        for (AstMemberDType* memp = structDtp->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            memberList.push_back(memp);
        }
        for (AstPatMember* itemp = VN_CAST(patp->itemsp(), PatMember); itemp;
             itemp = VN_CAST(itemp->nextp(), PatMember), ++posIdx) {
            string memberName;
            AstNodeDType* memberDtp = nullptr;
            // Try named key first
            if (AstText* const keyp = VN_CAST(itemp->keyp(), Text)) {
                const auto it = memberInfo.find(keyp->text());
                if (it != memberInfo.end()) {
                    memberName = it->second.first;
                    memberDtp = it->second.second;
                }
            }
            // Fall back to positional
            if (memberDtp == nullptr && posIdx < memberList.size()) {
                memberName = memberList[posIdx]->name();
                memberDtp = memberList[posIdx]->subDTypep();
            }
            if (!memberDtp) continue;
            string path = basePath.empty() ? memberName : basePath + "." + memberName;
            collectNestedPatternVars(itemp->lhssp(), memberDtp, path, out, tagChecks);
        }
    }

    // Get or build struct/union member map for O(1) lookups
    std::unordered_map<string, AstMemberDType*>& getStructMemberMap(AstNodeUOrStructDType* stp) {
        auto it = m_structMemberCache.find(stp);
        if (it != m_structMemberCache.end()) return it->second;
        auto& map = m_structMemberCache[stp];
        for (AstMemberDType* mp = stp->membersp(); mp; mp = VN_AS(mp->nextp(), MemberDType)) {
            map[mp->name()] = mp;
        }
        return map;
    }

    // Helper to find member dtype in a struct/union type - O(1) with cache
    AstNodeDType* findMemberDType(AstNodeDType* structDtp, const string& memberName) {
        AstNodeUOrStructDType* const stp = VN_CAST(structDtp->skipRefp(), NodeUOrStructDType);
        if (!stp) return nullptr;
        auto& map = getStructMemberMap(stp);
        auto it = map.find(memberName);
        return (it != map.end()) ? it->second->subDTypep() : nullptr;
    }

    // Build access expression from path: "field" -> .field, "[N]" -> [N]. O(P) where P = path
    // depth. Sets proper dtype on each intermediate node by walking the type hierarchy.
    AstNodeExpr* buildAccessExpr(FileLine* fl, AstNodeExpr* baseExpr, const string& path,
                                 AstNodeDType* finalDtypep) {
        AstNodeExpr* accessp = baseExpr->cloneTree(false);
        AstNodeDType* currentDtp = baseExpr->dtypep();
        size_t pos = 0;
        while (pos < path.size()) {
            if (path[pos] == '[') {
                // Array index: [N]
                size_t close = path.find(']', pos);
                int idx = std::stoi(path.substr(pos + 1, close - pos - 1));
                AstArraySel* const selp = new AstArraySel{fl, accessp, makeConst(fl, idx, 32)};
                // Get element type from array
                AstUnpackArrayDType* const arrDtp
                    = VN_CAST(currentDtp->skipRefp(), UnpackArrayDType);
                currentDtp = arrDtp ? arrDtp->subDTypep() : currentDtp;
                selp->dtypep(currentDtp);
                accessp = selp;
                pos = close + 1;
                pos += (pos < path.size() && path[pos] == '.') ? 1 : 0;
            } else {
                // Struct field access
                size_t next = path.find_first_of(".[", pos);
                if (next == string::npos) next = path.size();
                const string field = path.substr(pos, next - pos);
                AstStructSel* const selp = new AstStructSel{fl, accessp, field};
                // Look up member type
                AstNodeDType* const memberDtp = findMemberDType(currentDtp, field);
                if (memberDtp) currentDtp = memberDtp;
                selp->dtypep(currentDtp);
                accessp = selp;
                pos = (next < path.size() && path[next] == '.') ? next + 1 : next;
            }
        }
        // Set final dtype (may differ from tracked type due to further processing)
        accessp->dtypep(finalDtypep);
        return accessp;
    }

    // Result from handleNestedPattern
    struct NestedPatternResult VL_NOT_FINAL {
        AstVar* varDeclsp;  // Linked list of new variable declarations
        AstNode* assignsp;  // Linked list of assignments
    };

    // Handle nested pattern variables (struct or array). O(N) where N = pattern vars.
    // Creates new local variables, replaces references in bodyp, generates assignments.
    NestedPatternResult handleNestedPattern(FileLine* fl, AstNodeExpr* baseExpr, AstNode* bodyp,
                                            const std::vector<PatVarInfo>& vars) {
        AstNode* varDeclsp = nullptr;  // Use AstNode* to avoid strict-aliasing violation
        AstNode* assignsp = nullptr;
        for (const auto& var : vars) {
            // Find original placeholder variable
            AstVar* const origVarp = findPatternVarFromBody(bodyp, var.name);
            if (!origVarp) continue;
            // Create new local variable
            AstVar* const newVarp = new AstVar{fl, VVarType::BLOCKTEMP, var.name, var.dtypep};
            newVarp->funcLocal(true);
            addToNodeList(varDeclsp, newVarp);
            // Replace references to original with new variable
            replacePatternVarRefs(bodyp, origVarp, newVarp);
            // Build access expression and assignment
            AstNodeExpr* const accessp = buildAccessExpr(fl, baseExpr, var.accessPath, var.dtypep);
            AstVarRef* const varRefp = new AstVarRef{fl, newVarp, VAccess::WRITE};
            AstAssign* const assignp = new AstAssign{fl, varRefp, accessp};
            addToNodeList(assignsp, assignp);
        }
        return {VN_AS(varDeclsp, Var), assignsp};
    }

    // Handle simple pattern variable binding (tagged Member .var)
    // Returns pair of (varDecl, varAssign) or (nullptr, nullptr) if not applicable
    std::pair<AstVar*, AstAssign*> handleSimplePatternVar(const TaggedMatchContext& ctx,
                                                          AstNodeExpr* exprp,
                                                          const string& memberName,
                                                          AstPatternVar* patVarp) {
        const string& varName = patVarp->name();
        const int memberWidth = ctx.memberp->width();

        // Create local variable
        AstVar* varp;
        if (ctx.isUnpacked) {
            varp = new AstVar{ctx.fl, VVarType::BLOCKTEMP, varName, ctx.memberp->subDTypep()};
        } else {
            varp = new AstVar{ctx.fl, VVarType::BLOCKTEMP, varName, VFlagBitPacked{}, memberWidth};
        }
        varp->funcLocal(true);

        // Create data extraction and assignment
        AstNodeExpr* const exprClonep = exprp->cloneTree(false);
        AstNodeExpr* dataExtractp;
        if (ctx.isUnpacked) {
            dataExtractp = makeDataExtractUnpacked(ctx.fl, exprClonep, memberName,
                                                   ctx.memberp->subDTypep());
        } else {
            dataExtractp = makeDataExtract(ctx.fl, exprClonep, ctx.unionp, memberWidth);
            dataExtractp->dtypeSetBitSized(memberWidth, VSigning::UNSIGNED);
        }

        AstVarRef* const varRefp = new AstVarRef{ctx.fl, varp, VAccess::WRITE};
        AstAssign* const assignp = new AstAssign{ctx.fl, varRefp, dataExtractp};
        return {varp, assignp};
    }

    // Add a node to a linked list, handling null list case
    static void addToNodeList(AstNode*& listp, AstNode* nodep) {
        if (listp) {
            listp->addNext(nodep);
        } else {
            listp = nodep;
        }
    }

    // Build access expression from path for nested tag checks. O(P) where P = path depth.
    // Sets proper dtype on each intermediate StructSel by walking the type hierarchy.
    AstNodeExpr* buildTagCheckExpr(FileLine* fl, AstNodeExpr* baseExpr, const string& path) {
        AstNodeExpr* accessp = baseExpr->cloneTree(false);
        AstNodeDType* currentDtp = baseExpr->dtypep();
        UASSERT_OBJ(currentDtp, baseExpr, "baseExpr must have dtype");
        size_t pos = 0;
        while (pos < path.size()) {
            size_t next = path.find('.', pos);
            if (next == string::npos) next = path.size();
            const string field = path.substr(pos, next - pos);
            AstStructSel* const selp = new AstStructSel{fl, accessp, field};
            AstNodeDType* const memberDtp = findMemberDType(currentDtp, field);
            if (memberDtp) {
                selp->dtypep(memberDtp);
                currentDtp = memberDtp;
            }
            accessp = selp;
            pos = (next < path.size()) ? next + 1 : next;
        }
        // Access __Vtag field of the nested union
        AstStructSel* const tagSelp = new AstStructSel{fl, accessp, "__Vtag"};
        tagSelp->dtypeSetBitSized(32, VSigning::UNSIGNED);
        return tagSelp;
    }

    // Create combined condition for nested tag checks. O(N) where N = number of checks.
    AstNodeExpr* createNestedTagCondition(FileLine* fl, AstNodeExpr* baseExpr,
                                          const std::vector<NestedTagCheck>& checks,
                                          AstNodeExpr* outerCondp) {
        AstNodeExpr* condp = outerCondp;
        for (const auto& check : checks) {
            AstNodeExpr* const tagExprp = buildTagCheckExpr(fl, baseExpr, check.accessPath);
            AstConst* const tagConstp = makeConst(fl, check.tagIndex, 32);
            AstNodeExpr* const checkp = new AstEq{fl, tagExprp, tagConstp};
            checkp->dtypeSetBit();
            AstLogAnd* const combinedp = new AstLogAnd{fl, condp, checkp};
            combinedp->dtypeSetBit();
            condp = combinedp;
        }
        return condp;
    }

    // Build if-body combining assigns, original body, and optional guard
    // Note: When this is called, varAssignsp is always non-null (from handleSimplePatternVar)
    AstNode* buildInnerBody(AstNode* varAssignsp, AstNode* origBodyp, AstNodeExpr* guardp,
                            FileLine* fl) {
        UASSERT(varAssignsp, "buildInnerBody requires varAssignsp");
        if (guardp) {
            AstIf* const guardIfp = new AstIf{fl, guardp, origBodyp, nullptr};
            varAssignsp->addNext(guardIfp);
            return varAssignsp;
        }
        // origBodyp is always non-null (caller asserts thensp is non-null)
        varAssignsp->addNext(origBodyp);
        return varAssignsp;
    }

    // Build final if statement structure with all the various cases
    void buildFinalIfStatement(AstIf* ifp, FileLine* fl, AstNodeExpr* condp,
                               const IfBodyParts& parts) {
        if (parts.varDeclp) {
            // thensp is always non-null when we have a pattern variable:
            // - Parser creates empty AstBegin via newBlock() which never returns null
            // - V3LinkParse wraps thensp in begin block with pattern var declarations
            // - V3Begin may flatten empty body, but dead code optimization removes the
            //   entire if statement before V3Tagged runs in that case
            // elsesp may be null (no else clause)
            UASSERT_OBJ(ifp->thensp(), ifp, "thensp null with pattern variable");
            AstNode* const origBodyp = ifp->thensp()->unlinkFrBackWithNext();
            AstNode* origElsep = nullptr;
            if (ifp->elsesp()) origElsep = ifp->elsesp()->unlinkFrBackWithNext();
            AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};
            scopep->addStmtsp(parts.varDeclp);
            // origBodyp is always non-null (asserted above), origVarp may be null
            // if no VarRefs to the pattern variable were found in the body
            // Use & instead of && to avoid short-circuit branches for coverage
            if (parts.origVarp) replacePatternVarRefs(origBodyp, parts.origVarp, parts.varDeclp);
            if ((parts.origVarp != nullptr) & (parts.guardp != nullptr)) {
                replacePatternVarRefs(parts.guardp, parts.origVarp, parts.varDeclp);
            }
            AstNode* const innerBodyp
                = buildInnerBody(parts.varAssignsp, origBodyp, parts.guardp, fl);
            AstIf* const newIfp = new AstIf{fl, condp, innerBodyp, origElsep};
            scopep->addStmtsp(newIfp);
            ifp->replaceWith(scopep);
            VL_DO_DANGLING(pushDeletep(ifp), ifp);
            iterate(scopep);
            return;
        }
        // Note: parts.varAssignsp without parts.varDeclp is impossible
        // since handleSimplePatternVar() always sets both together
        if (parts.guardp) {
            // No pattern variable but have guard - AND the conditions
            AstLogAnd* const combinedCondp = new AstLogAnd{fl, condp, parts.guardp};
            combinedCondp->dtypeSetBit();
            ifp->condp(combinedCondp);
        } else {
            // No pattern variable, no guard - just use tag condition
            ifp->condp(condp);
        }
        iterate(ifp);
    }

    // Transform: if (expr matches tagged MemberName .var) body
    void transformIfMatches(AstIf* ifp, AstMatches* matchesp) {
        FileLine* const fl = matchesp->fileline();
        AstNodeExpr* const exprp = matchesp->lhsp();

        // Get the pattern - V3Width validates pattern is TaggedPattern or TaggedExpr
        AstTaggedPattern* const tagPatternp = VN_CAST(matchesp->patternp(), TaggedPattern);
        AstTaggedExpr* const tagExprp = VN_CAST(matchesp->patternp(), TaggedExpr);
        UASSERT_OBJ(tagPatternp || tagExprp, matchesp,
                    "V3Width ensures pattern is TaggedPattern/Expr");

        // Get union type - V3Width validates LHS is a tagged union
        AstUnionDType* const unionp = getMatchesUnionType(matchesp);
        UASSERT_OBJ(unionp && unionp->isTagged(), matchesp, "V3Width ensures tagged union type");

        // Lookup member (V3Width validates member exists)
        const string& memberName = tagPatternp ? tagPatternp->name() : tagExprp->name();
        AstMemberDType* const memberp = findMember(unionp, memberName);

        const bool isVoid = isVoidDType(memberp->subDTypep());
        const bool isUnpacked = !unionp->packed();

        // Create tag comparison
        AstNodeExpr* condp
            = createTagComparison(fl, exprp, unionp, memberp->tagIndex(), isUnpacked);

        // Handle pattern variable binding
        AstVar* varDeclp = nullptr;
        AstVar* origVarp = nullptr;
        AstNode* varAssignsp = nullptr;
        const TaggedMatchContext matchCtx{fl, unionp, memberp, isUnpacked};

        // Get guard expression before looking for pattern variable
        // (guard may contain VarRefs to the pattern variable)
        AstNodeExpr* guardp = matchesp->guardp();
        if (guardp) guardp = guardp->unlinkFrBack();

        // Get inner pattern from either TaggedPattern or TaggedExpr
        AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : tagExprp->exprp();
        if (innerPatternp && !VN_IS(innerPatternp, PatternStar) && !isVoid) {
            if (AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar)) {
                // Simple pattern variable binding
                origVarp = findPatternVarFromBody(ifp->thensp(), patVarp->name());
                if (!origVarp) origVarp = findPatternVarFromBody(guardp, patVarp->name());
                const auto result = handleSimplePatternVar(matchCtx, exprp, memberName, patVarp);
                varDeclp = result.first;
                varAssignsp = result.second;
            } else if (AstPattern* const structPatp = VN_CAST(innerPatternp, Pattern)) {
                // Nested pattern (struct or array) - collect pattern vars and nested tag checks
                std::vector<PatVarInfo> patVars;
                std::vector<NestedTagCheck> nestedTagChecks;
                collectNestedPatternVars(structPatp, memberp->subDTypep(), "", patVars,
                                         &nestedTagChecks);
                // Create base expression for member access
                AstNodeExpr* baseExprp = exprp->cloneTree(false);
                baseExprp = isUnpacked ? makeDataExtractUnpacked(fl, baseExprp, memberName,
                                                                 memberp->subDTypep())
                                       : baseExprp;
                // Add nested tag checks to condition
                condp = !nestedTagChecks.empty()
                            ? createNestedTagCondition(fl, baseExprp, nestedTagChecks, condp)
                            : condp;
                const auto result = handleNestedPattern(fl, baseExprp, ifp->thensp(), patVars);
                varDeclp = result.varDeclsp;
                varAssignsp = result.assignsp;
                // Delete baseExprp - it was only used as a template for cloning
                VL_DO_DANGLING(baseExprp->deleteTree(), baseExprp);
            }
        }

        // Delete the matches expression (always exists - it's the if condition)
        AstNodeExpr* oldCondp = matchesp->unlinkFrBack();
        UASSERT(oldCondp, "Matches expression should exist");
        VL_DO_DANGLING(oldCondp->deleteTree(), oldCondp);

        // Build and replace if statement
        const IfBodyParts parts{varDeclp, origVarp, varAssignsp, guardp};
        buildFinalIfStatement(ifp, fl, condp, parts);
        ++m_statTaggedMatches;
    }

    // Create temp variable for case matches expression
    AstVar* createCaseTempVar(FileLine* fl, AstUnionDType* unionp, bool isUnpacked) {
        AstVar* tempVarp;
        if (isUnpacked) {
            tempVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtagged_expr", unionp};
        } else {
            tempVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtagged_expr", VFlagBitPacked{},
                                  unionp->taggedTotalWidth()};
        }
        tempVarp->funcLocal(true);
        return tempVarp;
    }

    // Process a single tagged pattern in case matches, returns new case item
    // Always returns non-null when tagPatternp or tagExprCondp is valid
    AstCaseItem* processCaseTaggedPattern(const CaseMatchContext& ctx, AstCaseItem* itemp,
                                          AstNode* condp, AstNode*& varDeclsp) {
        AstTaggedPattern* const tagPatternp = VN_CAST(condp, TaggedPattern);
        AstTaggedExpr* const tagExprCondp = VN_CAST(condp, TaggedExpr);
        // V3Width validates conditions are TaggedPattern or TaggedExpr
        UASSERT_OBJ(tagPatternp || tagExprCondp, condp,
                    "V3Width validates case-matches conditions are tagged patterns");

        // V3Width validates member exists; one of tagPatternp/tagExprCondp is always set here
        const string& memberName = tagPatternp ? tagPatternp->name() : tagExprCondp->name();
        AstMemberDType* const memberp = findMember(ctx.unionp, memberName);

        const int tagConstWidth = ctx.isUnpacked ? 32 : ctx.tagWidth;
        AstConst* const tagConstp
            = makeConst(itemp->fileline(), memberp->tagIndex(), tagConstWidth);
        AstNode* stmtsp = nullptr;
        if (itemp->stmtsp()) stmtsp = itemp->stmtsp()->cloneTree(true);

        // Handle pattern variable binding with early returns
        // Get inner pattern from either TaggedPattern or TaggedExpr
        AstNode* const innerPatternp
            = tagPatternp ? tagPatternp->patternp() : tagExprCondp->exprp();
        // Evaluate both conditions to avoid short-circuit branch coverage gaps
        // VN_IS is null-safe, so evaluating with null innerPatternp is fine
        const bool noInnerPattern = !innerPatternp;
        const bool isPatternStar = VN_IS(innerPatternp, PatternStar);
        if (noInnerPattern || isPatternStar)
            return new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
        AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
        if (!patVarp) return new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
        // A void member cannot have a pattern variable binding (e.g., "tagged Invalid .x" is
        // invalid) V3Width should catch this, but assert defensively
        UASSERT_OBJ(!isVoidDType(memberp->subDTypep()), itemp,
                    "Void member cannot have pattern variable binding");

        // Create temp var reference and context, then get result
        AstVarRef* const tempRefp = new AstVarRef{ctx.fl, ctx.tempVarp, VAccess::READ};
        const TaggedMatchContext matchCtx{ctx.fl, ctx.unionp, memberp, ctx.isUnpacked};
        const auto result = handleSimplePatternVar(matchCtx, tempRefp, memberName, patVarp);
        VL_DO_DANGLING(tempRefp->deleteTree(), tempRefp);
        // handleSimplePatternVar always returns non-null pair
        AstVar* const varp = result.first;
        AstAssign* const assignp = result.second;
        UASSERT(varp, "handleSimplePatternVar must return varp");
        UASSERT(assignp, "handleSimplePatternVar must return assignp");

        addToNodeList(varDeclsp, varp);
        if (stmtsp) replacePatternVarRefs(stmtsp, patVarp->name(), varp);
        if (stmtsp) AstNode::addNext<AstNode, AstNode>(assignp, stmtsp);
        stmtsp = assignp;
        return new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
    }

    // Transform case matches statements
    void transformCaseMatches(AstCase* casep) {
        FileLine* const fl = casep->fileline();
        // V3Width validates expression is a tagged union
        AstUnionDType* const unionp = VN_CAST(casep->exprp()->dtypep()->skipRefp(), UnionDType);
        UASSERT_OBJ(unionp && unionp->isTagged(), casep, "V3Width ensures tagged union type");

        const bool isUnpacked = !unionp->packed();
        AstVar* const tempVarp = createCaseTempVar(fl, unionp, isUnpacked);
        AstAssign* const tempAssignp = new AstAssign{
            fl, new AstVarRef{fl, tempVarp, VAccess::WRITE}, casep->exprp()->cloneTree(false)};

        // Create tag extraction
        AstNodeExpr* const tagExprp
            = isUnpacked ? makeTagExtractUnpacked(fl, new AstVarRef{fl, tempVarp, VAccess::READ})
                         : makeTagExtract(fl, new AstVarRef{fl, tempVarp, VAccess::READ}, unionp);

        // Process case items
        AstNode* newCaseItemsp = nullptr;
        AstNode* varDeclsp = nullptr;
        const CaseMatchContext caseCtx{fl, unionp, tempVarp, isUnpacked, unionp->tagBitWidth()};

        for (AstCaseItem* itemp = casep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                AstCaseItem* const newItemp = new AstCaseItem{
                    itemp->fileline(), nullptr,
                    itemp->stmtsp() ? itemp->stmtsp()->cloneTree(true) : nullptr};
                addToNodeList(newCaseItemsp, newItemp);
                continue;
            }
            for (AstNode* condp = itemp->condsp(); condp; condp = condp->nextp()) {
                AstCaseItem* const newItemp
                    = processCaseTaggedPattern(caseCtx, itemp, condp, varDeclsp);
                // V3Width validates patterns; processCaseTaggedPattern always returns non-null
                addToNodeList(newCaseItemsp, newItemp);
            }
        }

        // Build final structure
        AstCase* const newCasep
            = new AstCase{fl, VCaseType::CT_CASE, tagExprp, VN_AS(newCaseItemsp, CaseItem)};
        AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};
        scopep->addStmtsp(tempVarp);
        if (varDeclsp) scopep->addStmtsp(varDeclsp);
        scopep->addStmtsp(tempAssignp);
        scopep->addStmtsp(newCasep);

        casep->replaceWith(scopep);
        VL_DO_DANGLING(pushDeletep(casep), casep);
        ++m_statTaggedMatches;
    }

    // Expand a nested tagged expression into field assignments. O(N) where N = pattern depth.
    // Generates: target.__Vtag = tagIndex; target.MemberName = value;
    void expandTaggedToAssigns(FileLine* fl, AstNodeExpr* targetp, AstTaggedExpr* taggedp,
                               AstUnionDType* unionp, AstNode*& assignsp) {
        AstMemberDType* const memberp = findMember(unionp, taggedp->name());
        const int tagIndex = memberp->tagIndex();
        const bool isVoid = isVoidDType(memberp->subDTypep());

        // target.__Vtag = tagIndex
        AstStructSel* const tagSelp = new AstStructSel{fl, targetp->cloneTree(false), "__Vtag"};
        tagSelp->dtypeSetBitSized(32, VSigning::UNSIGNED);
        AstAssign* const tagAssignp = new AstAssign{fl, tagSelp, makeConst(fl, tagIndex, 32)};
        addToNodeList(assignsp, tagAssignp);

        // If not void and has value, expand the member value
        if ((!isVoid) & (taggedp->exprp() != nullptr)) {
            AstStructSel* const memSelp
                = new AstStructSel{fl, targetp->cloneTree(false), taggedp->name()};
            memSelp->dtypep(memberp->subDTypep());
            expandValueToAssigns(fl, memSelp, taggedp->exprp(), memberp->subDTypep(), assignsp);
        }
    }

    // Expand struct pattern into field assignments. O(N) where N = pattern members.
    void expandPatternToAssigns(FileLine* fl, AstNodeExpr* targetp, AstPattern* patp,
                                AstNodeUOrStructDType* structDtp, AstNode*& assignsp) {
        // Build member lookup structures
        std::map<string, AstMemberDType*> memberMap;
        std::vector<AstMemberDType*> memberList;
        for (AstMemberDType* m = structDtp->membersp(); m; m = VN_AS(m->nextp(), MemberDType)) {
            memberMap[m->name()] = m;
            memberList.push_back(m);
        }

        // Iterate pattern members
        size_t idx = 0;
        for (AstPatMember* itemp = VN_CAST(patp->itemsp(), PatMember); itemp;
             itemp = VN_CAST(itemp->nextp(), PatMember), ++idx) {
            // Determine member name and type (by key or position)
            string memberName;
            AstMemberDType* memDtp = nullptr;
            if (AstText* const keyp = VN_CAST(itemp->keyp(), Text)) {
                const auto it = memberMap.find(keyp->text());
                if (it != memberMap.end()) {
                    memberName = it->first;
                    memDtp = it->second;
                }
            }
            if (!memDtp && idx < memberList.size()) {
                memberName = memberList[idx]->name();
                memDtp = memberList[idx];
            }
            if (!memDtp) continue;

            // Create target.memberName and recursively expand
            AstStructSel* const fieldSelp
                = new AstStructSel{fl, targetp->cloneTree(false), memberName};
            fieldSelp->dtypep(memDtp->subDTypep());
            expandValueToAssigns(fl, fieldSelp, itemp->lhssp(), memDtp->subDTypep(), assignsp);
        }
    }

    // Expand ConsPackUOrStruct (constant struct) into field assignments. O(N) where N = members.
    // V3Const converts Pattern to ConsPackUOrStruct before V3Tagged runs.
    void expandConsPackToAssigns(FileLine* fl, AstNodeExpr* targetp, AstConsPackUOrStruct* consp,
                                 AstNode*& assignsp) {
        for (AstConsPackMember* memp = consp->membersp(); memp;
             memp = VN_AS(memp->nextp(), ConsPackMember)) {
            // Get member info from dtype
            AstMemberDType* const memDtp = VN_AS(memp->dtypep(), MemberDType);
            UASSERT_OBJ(memDtp, memp, "ConsPackMember must have MemberDType");
            const string& memberName = memDtp->name();
            // Create target.memberName and recursively expand
            AstStructSel* const fieldSelp
                = new AstStructSel{fl, targetp->cloneTree(false), memberName};
            fieldSelp->dtypep(memDtp->subDTypep());
            expandValueToAssigns(fl, fieldSelp, memp->rhsp(), memDtp->subDTypep(), assignsp);
        }
    }

    // Recursively expand a value expression into field assignments. O(N) where N = pattern
    // elements. Handles patterns, nested tagged expressions, and simple expressions. targetp: the
    // target expression (e.g., o.Data.maybe) valuep: the value to assign (pattern, tagged expr, or
    // simple expr) dtypep: the expected type of the target assignsp: linked list of generated
    // assignments (output parameter)
    void expandValueToAssigns(FileLine* fl, AstNodeExpr* targetp, AstNode* valuep,
                              AstNodeDType* dtypep, AstNode*& assignsp) {
        // Check for nested tagged expression
        if (AstTaggedExpr* const nestedTaggedp = VN_CAST(valuep, TaggedExpr)) {
            // Try TaggedExpr's dtype first, fall back to passed dtypep
            AstNodeDType* exprDtp = nestedTaggedp->dtypep();
            if (!exprDtp) exprDtp = dtypep;
            AstUnionDType* const nestedUnionp
                = exprDtp ? VN_CAST(exprDtp->skipRefp(), UnionDType) : nullptr;
            if (nestedUnionp && !nestedUnionp->packed()) {
                expandTaggedToAssigns(fl, targetp, nestedTaggedp, nestedUnionp, assignsp);
                // targetp was used as template for cloning but not consumed
                VL_DO_DANGLING(targetp->deleteTree(), targetp);
                return;
            }
            // For packed unions, transform the expression and assign the result
            if (nestedUnionp && nestedUnionp->packed()) {
                AstNodeExpr* const transformedp = transformTaggedExpr(nestedTaggedp, nestedUnionp);
                AstAssign* const assignp = new AstAssign{fl, targetp, transformedp};
                addToNodeList(assignsp, assignp);
                return;
            }
            // Unknown union type - this shouldn't happen, assert
            UASSERT_OBJ(nestedUnionp, valuep, "TaggedExpr must have union dtype");
        }

        // Check for struct pattern
        if (AstPattern* const patp = VN_CAST(valuep, Pattern)) {
            AstNodeUOrStructDType* const structDtp
                = VN_CAST(dtypep->skipRefp(), NodeUOrStructDType);
            if (structDtp) {
                expandPatternToAssigns(fl, targetp, patp, structDtp, assignsp);
                // targetp was used as template for cloning but not consumed
                VL_DO_DANGLING(targetp->deleteTree(), targetp);
                return;
            }
        }

        // Check for ConsPackUOrStruct (Pattern converted by V3Const)
        if (AstConsPackUOrStruct* const consp = VN_CAST(valuep, ConsPackUOrStruct)) {
            expandConsPackToAssigns(fl, targetp, consp, assignsp);
            // targetp was used as template for cloning but not consumed
            VL_DO_DANGLING(targetp->deleteTree(), targetp);
            return;
        }

        // Simple expression - create direct assignment
        AstNodeExpr* const valueExprp = VN_AS(valuep, NodeExpr);
        UASSERT_OBJ(valueExprp, valuep, "Value must be expression");
        AstAssign* const assignp = new AstAssign{fl, targetp, valueExprp->cloneTree(false)};
        addToNodeList(assignsp, assignp);
    }

    // Check if a value contains nested unpacked tagged expressions. O(N).
    bool hasNestedUnpackedTagged(AstNode* nodep) {
        bool found = false;
        nodep->foreach([&](AstTaggedExpr* taggedp) {
            if (!found) {
                AstUnionDType* const unionp = VN_CAST(taggedp->dtypep()->skipRefp(), UnionDType);
                if (unionp && !unionp->packed()) found = true;
            }
        });
        return found;
    }

    // Transform: target = tagged MemberName (value)
    // For unpacked tagged unions, transforms into:
    //   target.__Vtag = tagIndex;
    //   target.MemberName = value;  // if not void (recursively expanded if nested)
    void transformTaggedExprUnpacked(AstAssign* assignp, AstTaggedExpr* taggedp,
                                     AstUnionDType* unionp) {
        FileLine* const fl = taggedp->fileline();

        // Get the target (LHS of assignment)
        AstNodeExpr* const targetp = assignp->lhsp();

        // Use expandTaggedToAssigns to handle all cases (simple and nested)
        AstNode* assignsp = nullptr;
        expandTaggedToAssigns(fl, targetp, taggedp, unionp, assignsp);

        // Replace original assignment with the generated assignments
        UASSERT(assignsp, "expandTaggedToAssigns must generate at least tag assignment");
        assignp->replaceWith(assignsp);
        VL_DO_DANGLING(pushDeletep(assignp), assignp);
    }

    // VISITORS
    void visit(AstTaggedExpr* nodep) override {
        // Note: TaggedExpr used as pattern in Matches expression is handled by
        // transformIfMatches() before this visitor sees it (via visit(AstIf*))

        // Get the union type from the expression's dtype
        // V3Width already validated: dtypep exists and is a tagged union
        AstNodeDType* const dtypep = nodep->dtypep();
        AstUnionDType* const unionp = VN_CAST(dtypep->skipRefp(), UnionDType);

        // For unpacked tagged unions, handle based on context
        if (!unionp->packed()) {
            // Check if direct RHS of assignment (simple check first)
            AstAssign* const directAssignp = VN_CAST(nodep->backp(), Assign);
            if (directAssignp && directAssignp->rhsp() == nodep) {
                transformTaggedExprUnpacked(directAssignp, nodep, unionp);
                ++m_statTaggedExprs;
                return;
            }
            // Not direct RHS - check if nested under an assignment (handled by outer expansion)
            if (isUnderAssignment(nodep)) return;
            nodep->v3warn(E_UNSUPPORTED, "Tagged expression in non-simple assignment context");
            return;
        }

        // Packed unions: iterate children first (for any nested packed tagged expressions)
        iterateChildren(nodep);

        // Transform tagged union expression (packed unions - use bit operations)
        AstNodeExpr* const newp = transformTaggedExpr(nodep, unionp);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        ++m_statTaggedExprs;
    }

    void visit(AstIf* nodep) override {
        // Check if this is an if with matches condition - let transformIfMatches validate the type
        if (AstMatches* const matchesp = VN_CAST(nodep->condp(), Matches)) {
            transformIfMatches(nodep, matchesp);
            return;
        }
        iterateChildren(nodep);
    }

    void visit(AstCase* nodep) override {
        // Check if this is a case matches - let transformCaseMatches validate the type
        if (nodep->caseMatches()) {
            transformCaseMatches(nodep);
            return;
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TaggedVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~TaggedVisitor() override {
        V3Stats::addStat("Tagged, expressions transformed", m_statTaggedExprs);
        V3Stats::addStat("Tagged, matches transformed", m_statTaggedMatches);
    }
};

//######################################################################
// Tagged class functions

void V3Tagged::taggedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TaggedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tagged", 0, dumpTreeEitherLevel() >= 3);
}
