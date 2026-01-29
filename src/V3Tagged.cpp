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
    AstMemberDType* findMember(AstUnionDType* unionp, const string& name) {
        auto& map = getUnionMemberMap(unionp);
        auto it = map.find(name);
        return (it != map.end()) ? it->second : nullptr;
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
        nodep->foreachAndNext([&](AstVarRef* varRefp) {
            if (!foundVarp && hasSuffix(varRefp->varp()->name(), suffix)) {
                foundVarp = varRefp->varp();
            }
        });
        return foundVarp;
    }

    // Replace all references to pattern variable with the new local variable
    // Uses O(1) pointer comparison when origVarp is provided
    void replacePatternVarRefs(AstNode* nodep, AstVar* origVarp, AstVar* newVarp) {
        nodep->foreachAndNext([&](AstVarRef* varRefp) {
            if (varRefp->varp() == origVarp) {
                varRefp->varp(newVarp);
                varRefp->name(newVarp->name());
            }
        });
    }

    // String-based overload for backwards compatibility (case matches)
    void replacePatternVarRefs(AstNode* nodep, const string& patternVarName, AstVar* newVarp) {
        const string suffix = "__DOT__" + patternVarName;
        nodep->foreachAndNext([&](AstVarRef* varRefp) {
            const string& refName = varRefp->varp()->name();
            if (refName == patternVarName || hasSuffix(refName, suffix)) {
                varRefp->varp(newVarp);
                varRefp->name(newVarp->name());
            }
        });
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
        AstNodeExpr* tagValp = makeConst(fl, tagIndex, totalWidth);
        if (maxMemberWidth > 0) {
            tagValp = new AstShiftL{fl, tagValp, makeConst(fl, maxMemberWidth, 32)};
            tagValp->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);
        }

        // Handle member value
        const bool isVoid = isVoidDType(memberp->subDTypep());
        if (isVoid || !nodep->exprp()) {
            // Void member or no expression - just return tag value
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
        if (maxMemberWidth < totalWidth) {
            valuep = new AstExtend{fl, valuep, totalWidth};
            valuep->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);
        }

        // Combine: tag | value
        AstNodeExpr* const resultp = new AstOr{fl, tagValp, valuep};
        resultp->dtypep(unionp);

        return resultp;
    }

    // Get tagged union type from matches expression
    AstUnionDType* getMatchesUnionType(AstMatches* matchesp) {
        AstNode* const patternp = matchesp->patternp();
        AstUnionDType* unionp = nullptr;
        if (VN_IS(patternp, TaggedPattern) || VN_IS(patternp, TaggedExpr)) {
            if (patternp->dtypep()) {
                unionp = VN_CAST(patternp->dtypep()->skipRefp(), UnionDType);
            }
        }
        if (!unionp) {
            AstNodeDType* const exprDtp = matchesp->lhsp()->dtypep()->skipRefp();
            unionp = VN_CAST(exprDtp, UnionDType);
        }
        return unionp;
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
            if (dataExtractp) dataExtractp->dtypeSetBitSized(memberWidth, VSigning::UNSIGNED);
        }

        if (!dataExtractp) return {varp, nullptr};

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

    // Build if-body combining assigns, original body, and optional guard
    AstNode* buildInnerBody(AstNode* varAssignsp, AstNode* origBodyp, AstNodeExpr* guardp,
                            FileLine* fl) {
        if (guardp) {
            AstIf* const guardIfp = new AstIf{fl, guardp, origBodyp, nullptr};
            if (!varAssignsp) return guardIfp;
            varAssignsp->addNext(guardIfp);
            return varAssignsp;
        }
        if (!varAssignsp) return origBodyp;
        if (origBodyp) varAssignsp->addNext(origBodyp);
        return varAssignsp;
    }

    // Build final if statement structure with all the various cases
    void buildFinalIfStatement(AstIf* ifp, FileLine* fl, AstNodeExpr* condp,
                               const IfBodyParts& parts) {
        if (parts.varDeclp) {
            AstNode* const origBodyp
                = ifp->thensp() ? ifp->thensp()->unlinkFrBackWithNext() : nullptr;
            AstNode* const origElsep
                = ifp->elsesp() ? ifp->elsesp()->unlinkFrBackWithNext() : nullptr;
            AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};
            scopep->addStmtsp(parts.varDeclp);
            if (origBodyp && parts.origVarp) {
                replacePatternVarRefs(origBodyp, parts.origVarp, parts.varDeclp);
            }
            if (parts.guardp && parts.origVarp) {
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

        // Get and validate union type
        AstUnionDType* const unionp = getMatchesUnionType(matchesp);
        if (!unionp || !unionp->isTagged()) {
            matchesp->v3error("Matches expression must be a tagged union type");
            return;
        }

        // Get the pattern
        AstTaggedPattern* const tagPatternp = VN_CAST(matchesp->patternp(), TaggedPattern);
        AstTaggedExpr* const tagExprp = VN_CAST(matchesp->patternp(), TaggedExpr);
        if (!tagPatternp && !tagExprp) {
            matchesp->v3error("Expected tagged pattern in matches expression");
            return;
        }

        // Lookup member
        const string& memberName = tagPatternp ? tagPatternp->name() : tagExprp->name();
        AstMemberDType* const memberp = findMember(unionp, memberName);
        if (!memberp) {
            matchesp->v3error("Tagged union member '" << memberName << "' not found");
            return;
        }

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

        AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : nullptr;
        if (innerPatternp && !VN_IS(innerPatternp, PatternStar)) {
            AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
            if (patVarp && !isVoid) {
                // Search the if body and guard to find the actual variable that VarRefs point to
                // This handles cases where V3Begin lifts variables with __DOT__ prefixes
                origVarp = findPatternVarFromBody(ifp->thensp(), patVarp->name());
                if (!origVarp) origVarp = findPatternVarFromBody(guardp, patVarp->name());
                const auto result = handleSimplePatternVar(matchCtx, exprp, memberName, patVarp);
                varDeclp = result.first;
                varAssignsp = result.second;
            }
        }

        // Delete the matches expression
        if (AstNodeExpr* oldCondp = matchesp->unlinkFrBack()) {
            VL_DO_DANGLING(oldCondp->deleteTree(), oldCondp);
        }

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
    AstCaseItem* processCaseTaggedPattern(const CaseMatchContext& ctx, AstCaseItem* itemp,
                                          AstNode* condp, AstNode*& varDeclsp) {
        AstTaggedPattern* const tagPatternp = VN_CAST(condp, TaggedPattern);
        AstTaggedExpr* const tagExprCondp = VN_CAST(condp, TaggedExpr);
        if (!tagPatternp && !tagExprCondp) return nullptr;

        const string& memberName = tagPatternp ? tagPatternp->name() : tagExprCondp->name();
        AstMemberDType* const memberp = findMember(ctx.unionp, memberName);
        if (!memberp) {
            condp->v3error("Tagged union member '" << memberName << "' not found");
            return nullptr;
        }

        const int tagConstWidth = ctx.isUnpacked ? 32 : ctx.tagWidth;
        AstConst* const tagConstp
            = makeConst(itemp->fileline(), memberp->tagIndex(), tagConstWidth);
        AstNode* stmtsp = itemp->stmtsp() ? itemp->stmtsp()->cloneTree(true) : nullptr;

        // Handle pattern variable binding with early returns
        AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : nullptr;
        if (!innerPatternp || VN_IS(innerPatternp, PatternStar))
            return new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
        AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
        if (!patVarp || isVoidDType(memberp->subDTypep()))
            return new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};

        // Create temp var reference and context, then get result
        AstVarRef* const tempRefp = new AstVarRef{ctx.fl, ctx.tempVarp, VAccess::READ};
        const TaggedMatchContext matchCtx{ctx.fl, ctx.unionp, memberp, ctx.isUnpacked};
        const auto result = handleSimplePatternVar(matchCtx, tempRefp, memberName, patVarp);
        VL_DO_DANGLING(tempRefp->deleteTree(), tempRefp);
        AstVar* const varp = result.first;
        AstAssign* const assignp = result.second;

        if (varp) addToNodeList(varDeclsp, varp);
        if (assignp) {
            if (stmtsp) replacePatternVarRefs(stmtsp, patVarp->name(), varp);
            if (stmtsp) AstNode::addNext<AstNode, AstNode>(assignp, stmtsp);
            stmtsp = assignp;
        }
        return new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
    }

    // Transform case matches statements
    void transformCaseMatches(AstCase* casep) {
        FileLine* const fl = casep->fileline();
        AstUnionDType* const unionp = VN_CAST(casep->exprp()->dtypep()->skipRefp(), UnionDType);

        if (!unionp || !unionp->isTagged()) {
            casep->v3error("Case matches expression must be a tagged union type");
            return;
        }

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
                if (newItemp) addToNodeList(newCaseItemsp, newItemp);
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

    // Transform: target = tagged MemberName (value)
    // For unpacked tagged unions, transforms into:
    //   target.__Vtag = tagIndex;
    //   target.MemberName = value;  // if not void
    void transformTaggedExprUnpacked(AstAssign* assignp, AstTaggedExpr* taggedp,
                                     AstUnionDType* unionp) {
        FileLine* const fl = taggedp->fileline();
        AstMemberDType* const memberp = findMember(unionp, taggedp->name());
        // memberp validity checked by V3Width before V3Tagged runs

        const int tagIndex = memberp->tagIndex();
        const bool isVoid = isVoidDType(memberp->subDTypep());

        // Get the target (LHS of assignment) and clone it
        AstNodeExpr* const targetp = assignp->lhsp();

        // Create: target.__Vtag = tagIndex
        AstStructSel* const tagSelp = new AstStructSel{fl, targetp->cloneTree(false), "__Vtag"};
        tagSelp->dtypeSetBitSized(32, VSigning::UNSIGNED);
        AstAssign* const tagAssignp = new AstAssign{fl, tagSelp, makeConst(fl, tagIndex, 32)};

        // Replace the original assignment with tag assignment
        assignp->replaceWith(tagAssignp);

        // If member is not void, add member assignment after tag assignment
        if (!isVoid && taggedp->exprp()) {
            AstStructSel* const memberSelp
                = new AstStructSel{fl, targetp->cloneTree(false), taggedp->name()};
            memberSelp->dtypep(memberp->subDTypep());
            // Clone the value expression to avoid dtype reference issues when original tree is
            // deleted
            AstNodeExpr* valuep = taggedp->exprp()->cloneTree(false);
            AstAssign* const memberAssignp = new AstAssign{fl, memberSelp, valuep};
            tagAssignp->addNextHere(memberAssignp);
        }

        VL_DO_DANGLING(pushDeletep(assignp), assignp);
    }

    // VISITORS
    void visit(AstTaggedExpr* nodep) override {
        // Don't iterate children - we handle exprp directly in the transform
        // iterateChildren(nodep);

        // Skip transformation if this TaggedExpr is used as a pattern in a Matches expression
        // In that case, transformIfMatches() will handle it
        if (AstMatches* const matchesp = VN_CAST(nodep->backp(), Matches)) {
            if (matchesp->patternp() == nodep) {
                // This is a pattern, not an expression to be transformed
                // transformIfMatches() will handle it when processing the parent If
                return;
            }
        }

        // Get the union type from the expression's dtype
        // V3Width already validated: dtypep exists and is a tagged union
        AstNodeDType* const dtypep = nodep->dtypep();
        AstUnionDType* const unionp = VN_CAST(dtypep->skipRefp(), UnionDType);

        // For unpacked tagged unions, handle at assignment level
        // This includes explicitly unpacked unions and those with dynamic/array members
        if (!unionp->packed()) {
            // Find parent assignment
            AstAssign* const assignp = VN_CAST(nodep->backp(), Assign);
            if (assignp && assignp->rhsp() == nodep) {
                transformTaggedExprUnpacked(assignp, nodep, unionp);
                ++m_statTaggedExprs;
                return;
            }
            // If not in simple assignment context, this is more complex
            // For now, emit an error for unsupported contexts
            nodep->v3warn(E_UNSUPPORTED, "Tagged expression in non-simple assignment context");
            return;
        }

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
