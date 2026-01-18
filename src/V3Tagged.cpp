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

    // METHODS
    // Find a member in the tagged union by name
    AstMemberDType* findMember(AstUnionDType* unionp, const string& name) {
        for (AstMemberDType* itemp = unionp->membersp(); itemp;
             itemp = VN_AS(itemp->nextp(), MemberDType)) {
            if (itemp->name() == name) return itemp;
        }
        return nullptr;
    }

    // Check if a dtype is void
    bool isVoidDType(AstNodeDType* dtp) {
        dtp = dtp->skipRefp();
        return VN_IS(dtp, BasicDType)
               && VN_AS(dtp, BasicDType)->keyword() == VBasicDTypeKwd::CVOID;
    }

    // Check if a dtype is a dynamic type that can't be bit-packed
    // (real, shortreal, string, chandle, class, event)
    bool isDynamicDType(AstNodeDType* dtp) {
        dtp = dtp->skipRefp();
        if (AstBasicDType* const basicp = VN_CAST(dtp, BasicDType)) {
            const VBasicDTypeKwd kwd = basicp->keyword();
            return kwd == VBasicDTypeKwd::DOUBLE || kwd == VBasicDTypeKwd::STRING
                   || kwd == VBasicDTypeKwd::CHANDLE || kwd == VBasicDTypeKwd::EVENT;
        }
        // Class types are also dynamic
        if (VN_IS(dtp, ClassRefDType)) return true;
        return false;
    }

    // Check if union has any dynamic type members
    bool hasDynamicMember(AstUnionDType* unionp) {
        for (AstMemberDType* memberp = unionp->membersp(); memberp;
             memberp = VN_AS(memberp->nextp(), MemberDType)) {
            if (isDynamicDType(memberp->subDTypep())) return true;
        }
        return false;
    }

    // Find AstVar by name in begin block or module containing the if statement
    AstVar* findPatternVar(AstIf* ifp, const string& varName) {
        // The variable may be in:
        // 1. A begin block that is a parent of the if (before V3Begin)
        // 2. The module scope (after V3Begin moves vars to module level)
        // Name may be mangled with scope prefix like "unnamedblk1__DOT__a"
        const string suffix = "__DOT__" + varName;
        AstNodeModule* modulep = nullptr;
        for (AstNode* parentp = ifp->backp(); parentp; parentp = parentp->backp()) {
            if (AstBegin* const beginp = VN_CAST(parentp, Begin)) {
                // Search statements in begin for the variable
                for (AstNode* stmtp = beginp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                        const string& varpName = varp->name();
                        // Match exact name or mangled name ending with __DOT__<varName>
                        if (varpName == varName
                            || (varpName.size() > suffix.size()
                                && varpName.substr(varpName.size() - suffix.size()) == suffix)) {
                            return varp;
                        }
                    }
                }
            }
            // Remember the module for later search
            if (AstNodeModule* const modp = VN_CAST(parentp, NodeModule)) {
                modulep = modp;
                break;
            }
            // Stop at function boundary but continue searching
            if (VN_IS(parentp, NodeFTask)) break;
        }
        // Also search module-level vars (V3Begin moves vars from begin blocks to module)
        if (modulep) {
            for (AstNode* stmtp = modulep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                    const string& varpName = varp->name();
                    if (varpName == varName
                        || (varpName.size() > suffix.size()
                            && varpName.substr(varpName.size() - suffix.size()) == suffix)) {
                        return varp;
                    }
                }
            }
        }
        return nullptr;
    }

    // Replace all references to pattern variable with the new local variable
    void replacePatternVarRefs(AstNode* nodep, const string& patternVarName, AstVar* newVarp) {
        if (!nodep) return;
        // Check this node
        if (AstVarRef* const varRefp = VN_CAST(nodep, VarRef)) {
            // Match by base name (pattern variable name might be mangled with prefix)
            const string& refName = varRefp->varp()->name();
            // Check if the reference ends with __DOT__<patternVarName>
            // or if it's exactly the pattern variable name
            const string suffix = "__DOT__" + patternVarName;
            if (refName == patternVarName
                || (refName.size() > suffix.size()
                    && refName.substr(refName.size() - suffix.size()) == suffix)) {
                // Update the reference to point to the new variable
                varRefp->varp(newVarp);
                varRefp->name(newVarp->name());
            }
        }
        // Recurse into children
        if (nodep->op1p()) replacePatternVarRefs(nodep->op1p(), patternVarName, newVarp);
        if (nodep->op2p()) replacePatternVarRefs(nodep->op2p(), patternVarName, newVarp);
        if (nodep->op3p()) replacePatternVarRefs(nodep->op3p(), patternVarName, newVarp);
        if (nodep->op4p()) replacePatternVarRefs(nodep->op4p(), patternVarName, newVarp);
        // Recurse to siblings
        if (nodep->nextp()) replacePatternVarRefs(nodep->nextp(), patternVarName, newVarp);
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
        if (memberWidth == 0) return nullptr;  // Void member
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
        UASSERT_OBJ(memberp, nodep, "Member not found in tagged union");

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
        } else if (memberWidth > maxMemberWidth) {
            // Truncate - shouldn't happen but handle defensively
            valuep = new AstSel{fl, valuep, 0, maxMemberWidth};
            valuep->dtypeSetBitSized(maxMemberWidth, VSigning::UNSIGNED);
        }

        // Extend value to total width for OR operation
        if (maxMemberWidth < totalWidth) {
            valuep = new AstExtend{fl, valuep, totalWidth};
            valuep->dtypeSetBitSized(totalWidth, VSigning::UNSIGNED);
        }

        // Combine: tag | value
        AstNodeExpr* resultp = new AstOr{fl, tagValp, valuep};
        resultp->dtypep(unionp);

        return resultp;
    }

    // Transform pattern variable binding into a local variable declaration
    // Returns the variable that was created
    AstVar* createPatternVarBinding(FileLine* fl, const string& varName, AstNodeDType* dtypep,
                                    AstNode* stmtsp) {
        // Create a local variable for the pattern variable
        AstVar* const varp = new AstVar{fl, VVarType::BLOCKTEMP, varName, dtypep};
        varp->funcLocal(true);
        return varp;
    }

    // Transform: if (expr matches tagged MemberName .var) body
    // Into: { type var; if ((expr >> maxMemberW) == tagVal) { var = expr[0 +: memberW]; body } }
    void transformIfMatches(AstIf* ifp, AstMatches* matchesp) {
        FileLine* const fl = matchesp->fileline();

        // Get the expression being matched
        AstNodeExpr* const exprp = matchesp->lhsp();

        // Get the union type - try pattern first (TaggedExpr/TaggedPattern have union dtype),
        // then fall back to LHS expression's dtype
        AstNode* const patternp = matchesp->patternp();
        AstUnionDType* unionp = nullptr;
        if (VN_IS(patternp, TaggedPattern) || VN_IS(patternp, TaggedExpr)) {
            if (patternp->dtypep()) {
                unionp = VN_CAST(patternp->dtypep()->skipRefp(), UnionDType);
            }
        }
        if (!unionp) {
            AstNodeDType* const exprDtp = exprp->dtypep()->skipRefp();
            unionp = VN_CAST(exprDtp, UnionDType);
        }

        if (!unionp || !unionp->isTagged()) {
            matchesp->v3error("Matches expression must be a tagged union type");
            return;
        }

        // Get the pattern - can be either AstTaggedPattern (with binding) or AstTaggedExpr (no
        // binding)
        AstTaggedPattern* const tagPatternp = VN_CAST(matchesp->patternp(), TaggedPattern);
        AstTaggedExpr* const tagExprp = VN_CAST(matchesp->patternp(), TaggedExpr);
        if (!tagPatternp && !tagExprp) {
            matchesp->v3error("Expected tagged pattern in matches expression");
            return;
        }

        const string& memberName = tagPatternp ? tagPatternp->name() : tagExprp->name();
        AstMemberDType* const memberp = findMember(unionp, memberName);
        if (!memberp) {
            matchesp->v3error("Tagged union member '" << memberName << "' not found");
            return;
        }

        const int tagIndex = memberp->tagIndex();
        const int tagWidth = unionp->tagBitWidth();
        const bool isVoid = isVoidDType(memberp->subDTypep());
        const bool isUnpacked = !unionp->packed();

        // Create tag comparison
        // For packed: (expr >> maxMemberWidth) == tagIndex
        // For unpacked: expr.__Vtag == tagIndex
        AstNodeExpr* const exprClonep = exprp->cloneTree(false);
        AstNodeExpr* tagExtractp;
        AstNodeExpr* tagConstp;
        if (isUnpacked) {
            tagExtractp = makeTagExtractUnpacked(fl, exprClonep);
            tagConstp = makeConst(fl, tagIndex, 32);
        } else {
            tagExtractp = makeTagExtract(fl, exprClonep, unionp);
            tagConstp = makeConst(fl, tagIndex, tagWidth);
        }
        AstNodeExpr* condp = new AstEq{fl, tagExtractp, tagConstp};
        condp->dtypeSetBit();

        // Handle pattern variable binding (only if we have an AstTaggedPattern with inner pattern)
        AstNode* varDeclsp = nullptr;
        AstNode* varAssignsp = nullptr;

        AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : nullptr;
        if (innerPatternp && !VN_IS(innerPatternp, PatternStar)) {
            AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
            if (patVarp && !isVoid) {
                const string& varName = patVarp->name();
                const int memberWidth = memberp->width();

                // Create local variable
                // For unpacked: use actual member dtype
                // For packed: use bit-packed type
                AstVar* varp;
                if (isUnpacked) {
                    // Use direct dtype - V3Width has already run so VFlagChildDType won't work
                    varp = new AstVar{fl, VVarType::BLOCKTEMP, varName, memberp->subDTypep()};
                } else {
                    varp = new AstVar{fl, VVarType::BLOCKTEMP, varName, VFlagBitPacked{},
                                      memberWidth};
                }
                varp->funcLocal(true);
                varDeclsp = varp;

                // Create assignment
                // For unpacked: var = expr.MemberName
                // For packed: var = expr[0 +: memberWidth]
                AstNodeExpr* const exprClone2p = exprp->cloneTree(false);
                AstNodeExpr* dataExtractp;
                if (isUnpacked) {
                    dataExtractp = makeDataExtractUnpacked(fl, exprClone2p, memberName,
                                                           memberp->subDTypep());
                } else {
                    dataExtractp = makeDataExtract(fl, exprClone2p, unionp, memberWidth);
                    if (dataExtractp) {
                        dataExtractp->dtypeSetBitSized(memberWidth, VSigning::UNSIGNED);
                    }
                }
                if (dataExtractp) {
                    AstVarRef* const varRefp = new AstVarRef{fl, varp, VAccess::WRITE};
                    AstAssign* const assignp = new AstAssign{fl, varRefp, dataExtractp};
                    varAssignsp = assignp;
                }
            }
            // Handle struct pattern inside TaggedPattern: tagged Member '{field:.var, ...}
            else if (AstPattern* const structPatp = VN_CAST(innerPatternp, Pattern)) {
                // Member type should be a struct
                AstNodeDType* const memberDtp = memberp->subDTypep()->skipRefp();
                AstNodeUOrStructDType* const structDtp = VN_CAST(memberDtp, NodeUOrStructDType);
                if (structDtp) {
                    // Extract the whole struct first
                    AstNodeExpr* const exprClone2p = exprp->cloneTree(false);
                    AstNodeExpr* dataExtractp;
                    if (isUnpacked) {
                        dataExtractp = makeDataExtractUnpacked(fl, exprClone2p, memberName,
                                                               memberp->subDTypep());
                    } else {
                        dataExtractp = makeDataExtract(fl, exprClone2p, unionp, memberp->width());
                        if (dataExtractp) { dataExtractp->dtypep(structDtp); }
                    }

                    // For each PatMember containing a PatternVar, create assignment
                    for (AstPatMember* patMemp = VN_CAST(structPatp->itemsp(), PatMember); patMemp;
                         patMemp = VN_CAST(patMemp->nextp(), PatMember)) {
                        AstPatternVar* const patVarp = VN_CAST(patMemp->lhssp(), PatternVar);
                        if (patVarp) {
                            // Get field name from key
                            const AstText* const keyTextp = VN_CAST(patMemp->keyp(), Text);
                            if (keyTextp) {
                                // Find the struct field by name
                                for (AstMemberDType* fieldp = structDtp->membersp(); fieldp;
                                     fieldp = VN_AS(fieldp->nextp(), MemberDType)) {
                                    if (fieldp->name() == keyTextp->text()) {
                                        const string& varName = patVarp->name();

                                        // var = extractedStruct.fieldName
                                        AstNodeExpr* const structClonep
                                            = dataExtractp->cloneTree(false);
                                        AstNodeExpr* fieldExtractp;
                                        if (isUnpacked) {
                                            fieldExtractp = new AstStructSel{fl, structClonep,
                                                                             fieldp->name()};
                                            fieldExtractp->dtypep(fieldp->subDTypep());
                                        } else {
                                            const int fieldLsb = fieldp->lsb();
                                            const int fieldWidth = fieldp->width();
                                            fieldExtractp = new AstSel{fl, structClonep, fieldLsb,
                                                                       fieldWidth};
                                            fieldExtractp->dtypeSetBitSized(fieldWidth,
                                                                            VSigning::UNSIGNED);
                                        }

                                        // Find the actual variable (V3LinkParse created it)
                                        AstVar* const varp = findPatternVar(ifp, varName);
                                        if (!varp) {
                                            VL_DO_DANGLING(fieldExtractp->deleteTree(),
                                                           fieldExtractp);
                                            break;
                                        }
                                        AstVarRef* const varRefp
                                            = new AstVarRef{fl, varp, VAccess::WRITE};
                                        AstAssign* const assignp
                                            = new AstAssign{fl, varRefp, fieldExtractp};
                                        if (varAssignsp) {
                                            varAssignsp->addNext(assignp);
                                        } else {
                                            varAssignsp = assignp;
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    // Clean up cloned data extract if not used
                    if (!varAssignsp) { VL_DO_DANGLING(dataExtractp->deleteTree(), dataExtractp); }
                }
            }
        }

        // Handle TaggedExpr with struct pattern containing pattern variables
        // Grammar creates TaggedExpr when pattern is '{...} with PatternVars
        if (tagExprp && !isVoid) {
            // Check if exprp contains struct pattern with pattern variables
            AstConsPackUOrStruct* const structp = VN_CAST(tagExprp->exprp(), ConsPackUOrStruct);
            if (structp) {
                // Member type should be a struct
                AstNodeDType* const memberDtp = memberp->subDTypep()->skipRefp();
                AstNodeUOrStructDType* const structDtp = VN_CAST(memberDtp, NodeUOrStructDType);
                if (structDtp) {
                    // Extract the whole struct first
                    AstNodeExpr* const exprClone2p = exprp->cloneTree(false);
                    AstNodeExpr* dataExtractp;
                    if (isUnpacked) {
                        dataExtractp = makeDataExtractUnpacked(fl, exprClone2p, memberName,
                                                               memberp->subDTypep());
                    } else {
                        dataExtractp = makeDataExtract(fl, exprClone2p, unionp, memberp->width());
                        if (dataExtractp) { dataExtractp->dtypep(structDtp); }
                    }

                    // For each ConsPackMember containing a PatternVar, create assignment
                    for (AstConsPackMember* cpm = structp->membersp(); cpm;
                         cpm = VN_CAST(cpm->nextp(), ConsPackMember)) {
                        // Find PatternVar inside (may be inside Extend)
                        AstNode* valuep = cpm->rhsp();
                        while (AstExtend* extp = VN_CAST(valuep, Extend)) {
                            valuep = extp->lhsp();
                        }
                        AstPatternVar* const patVarp = VN_CAST(valuep, PatternVar);
                        if (patVarp) {
                            // Get field type from ConsPackMember
                            AstMemberDType* const fieldDtp = VN_CAST(cpm->dtypep(), MemberDType);
                            if (fieldDtp) {
                                const string& varName = patVarp->name();

                                // Variable is already declared by V3LinkParse
                                // We just need to create the assignment
                                // var = extractedStruct.fieldName
                                AstNodeExpr* const structClonep = dataExtractp->cloneTree(false);
                                AstNodeExpr* fieldExtractp;
                                if (isUnpacked) {
                                    // For unpacked: use struct member access
                                    fieldExtractp
                                        = new AstStructSel{fl, structClonep, fieldDtp->name()};
                                    fieldExtractp->dtypep(fieldDtp->subDTypep());
                                } else {
                                    // For packed: extract bits from the packed struct
                                    const int fieldLsb = fieldDtp->lsb();
                                    const int fieldWidth = fieldDtp->width();
                                    fieldExtractp
                                        = new AstSel{fl, structClonep, fieldLsb, fieldWidth};
                                    fieldExtractp->dtypeSetBitSized(fieldWidth,
                                                                    VSigning::UNSIGNED);
                                }

                                // Create assignment: patternVar = fieldValue
                                // Find the actual variable (V3LinkParse created it)
                                // Note: V3LinkParse only creates VARs for pattern variables
                                // that are actually used in the body, so unused pattern vars
                                // won't have a VAR - that's fine, just skip them
                                AstVar* const varp = findPatternVar(ifp, varName);
                                if (!varp) {
                                    // Pattern variable is unused - clean up and skip
                                    VL_DO_DANGLING(fieldExtractp->deleteTree(), fieldExtractp);
                                    continue;
                                }
                                AstVarRef* const varRefp = new AstVarRef{fl, varp, VAccess::WRITE};
                                AstAssign* const assignp
                                    = new AstAssign{fl, varRefp, fieldExtractp};
                                if (varAssignsp) {
                                    varAssignsp->addNext(assignp);
                                } else {
                                    varAssignsp = assignp;
                                }
                            }
                        }
                    }
                    // Clean up cloned data extract if not used
                    if (!varAssignsp) { VL_DO_DANGLING(dataExtractp->deleteTree(), dataExtractp); }
                }
            }
            // Also handle Pattern with PatMember children
            // (inner matches may parse '{...} as Pattern not ConsPackUOrStruct)
            else if (AstPattern* const patternp = VN_CAST(tagExprp->exprp(), Pattern)) {
                // Member type should be a struct
                AstNodeDType* const memberDtp = memberp->subDTypep()->skipRefp();
                AstNodeUOrStructDType* const structDtp = VN_CAST(memberDtp, NodeUOrStructDType);
                if (structDtp) {
                    // Extract the whole struct first
                    AstNodeExpr* const exprClone2p = exprp->cloneTree(false);
                    AstNodeExpr* dataExtractp;

                    // For anonymous structs in unions, member widths and LSBs may not be
                    // set correctly. Compute them from member definitions.
                    // SystemVerilog: first member in struct is at high bits
                    std::map<string, std::pair<int, int>> fieldInfo;  // name -> (lsb, width)
                    int bitOffset = 0;
                    // First pass: collect all widths
                    std::vector<std::pair<string, int>> fieldOrder;
                    for (AstMemberDType* mp = structDtp->membersp(); mp;
                         mp = VN_AS(mp->nextp(), MemberDType)) {
                        fieldOrder.emplace_back(mp->name(), mp->width());
                    }
                    // Second pass: compute LSBs (last member is at LSB 0)
                    for (auto it = fieldOrder.rbegin(); it != fieldOrder.rend(); ++it) {
                        fieldInfo[it->first] = std::make_pair(bitOffset, it->second);
                        bitOffset += it->second;
                    }
                    const int structWidth = bitOffset;

                    if (isUnpacked) {
                        dataExtractp = makeDataExtractUnpacked(fl, exprClone2p, memberName,
                                                               memberp->subDTypep());
                    } else {
                        dataExtractp = makeDataExtract(fl, exprClone2p, unionp, structWidth);
                        if (dataExtractp) { dataExtractp->dtypep(structDtp); }
                    }

                    // For each PatMember containing a PatternVar, create assignment
                    for (AstPatMember* patMemp = VN_CAST(patternp->itemsp(), PatMember); patMemp;
                         patMemp = VN_CAST(patMemp->nextp(), PatMember)) {
                        AstPatternVar* const patVarp = VN_CAST(patMemp->lhssp(), PatternVar);
                        if (patVarp) {
                            // Get field name from key
                            const AstText* const keyTextp = VN_CAST(patMemp->keyp(), Text);
                            if (keyTextp) {
                                // Find the struct field by name
                                for (AstMemberDType* fieldp = structDtp->membersp(); fieldp;
                                     fieldp = VN_AS(fieldp->nextp(), MemberDType)) {
                                    if (fieldp->name() == keyTextp->text()) {
                                        const string& varName = patVarp->name();
                                        // Use computed field info since anonymous struct lsb may
                                        // be -1
                                        const auto& fi = fieldInfo[fieldp->name()];
                                        const int fieldLsb = fi.first;
                                        const int fieldWidth = fi.second;

                                        // var = extractedStruct.fieldName
                                        AstNodeExpr* const structClonep
                                            = dataExtractp->cloneTree(false);
                                        AstNodeExpr* fieldExtractp;
                                        if (isUnpacked) {
                                            fieldExtractp = new AstStructSel{fl, structClonep,
                                                                             fieldp->name()};
                                            fieldExtractp->dtypep(fieldp->subDTypep());
                                        } else {
                                            fieldExtractp = new AstSel{fl, structClonep, fieldLsb,
                                                                       fieldWidth};
                                            fieldExtractp->dtypeSetBitSized(fieldWidth,
                                                                            VSigning::UNSIGNED);
                                        }

                                        // Find the actual variable (V3LinkParse created it)
                                        AstVar* const varp = findPatternVar(ifp, varName);
                                        if (!varp) {
                                            VL_DO_DANGLING(fieldExtractp->deleteTree(),
                                                           fieldExtractp);
                                            break;
                                        }
                                        AstVarRef* const varRefp
                                            = new AstVarRef{fl, varp, VAccess::WRITE};
                                        AstAssign* const assignp
                                            = new AstAssign{fl, varRefp, fieldExtractp};
                                        if (varAssignsp) {
                                            varAssignsp->addNext(assignp);
                                        } else {
                                            varAssignsp = assignp;
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    // Clean up cloned data extract if not used
                    if (!varAssignsp) { VL_DO_DANGLING(dataExtractp->deleteTree(), dataExtractp); }
                }
            }
        }

        // Get guard expression if present (&&& expr) BEFORE deleting matchesp
        AstNodeExpr* guardp = matchesp->guardp();
        if (guardp) guardp = guardp->unlinkFrBack();

        // Replace the condition (deletes matchesp)
        if (AstNodeExpr* oldCondp = matchesp->unlinkFrBack()) {
            VL_DO_DANGLING(oldCondp->deleteTree(), oldCondp);
        }

        // Add variable declaration and assignment
        if (varDeclsp) {
            // Wrap in a C++ local scope for the pattern variable
            AstNode* const origBodyp
                = ifp->thensp() ? ifp->thensp()->unlinkFrBackWithNext() : nullptr;
            AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};

            // Add variable declaration
            AstVar* const varp = VN_AS(varDeclsp, Var);
            scopep->addStmtsp(varDeclsp);

            // Replace pattern variable references in original body
            if (origBodyp && varp) { replacePatternVarRefs(origBodyp, varp->name(), varp); }

            // If there's a guard with pattern variable, update references in the guard
            // guardp is already unlinked, no need to clone
            if (guardp && varp) { replacePatternVarRefs(guardp, varp->name(), varp); }

            // Build the body
            // If guard present: assignment + if(guard) { original body }
            // If no guard: assignment + original body
            AstNode* innerBodyp;
            if (guardp) {
                // Create inner if for guard
                AstIf* const guardIfp = new AstIf{fl, guardp, origBodyp, nullptr};
                innerBodyp = varAssignsp;
                if (innerBodyp) {
                    innerBodyp->addNext(guardIfp);
                } else {
                    innerBodyp = guardIfp;
                }
            } else {
                innerBodyp = varAssignsp;
                if (origBodyp) {
                    if (innerBodyp) {
                        innerBodyp->addNext(origBodyp);
                    } else {
                        innerBodyp = origBodyp;
                    }
                }
            }

            // Create new if statement with tag condition
            AstIf* const newIfp = new AstIf{fl, condp, innerBodyp, nullptr};

            // Replace original if with local scope containing var + new if
            scopep->addStmtsp(newIfp);
            ifp->replaceWith(scopep);
            VL_DO_DANGLING(pushDeletep(ifp), ifp);
            // Iterate the new structure to transform any nested matches expressions
            // (e.g., guard expression that is itself a matches expression)
            iterate(scopep);
        } else if (varAssignsp) {
            // Have assignments but no new variable declarations (struct pattern case)
            // Variables were already declared by V3LinkParse in parent begin block
            AstNode* origBodyp = ifp->thensp() ? ifp->thensp()->unlinkFrBackWithNext() : nullptr;
            AstNode* origElsep = ifp->elsesp() ? ifp->elsesp()->unlinkFrBackWithNext() : nullptr;

            // Build the body: assignments + original body
            AstNode* newBodyp = varAssignsp;
            if (origBodyp) newBodyp->addNext(origBodyp);

            // Handle guard if present
            if (guardp) {
                // Create inner if for guard
                AstIf* const guardIfp = new AstIf{fl, guardp, newBodyp, nullptr};
                newBodyp = guardIfp;
            }

            // Create new if with tag condition
            AstIf* const newIfp = new AstIf{fl, condp, newBodyp, origElsep};
            ifp->replaceWith(newIfp);
            VL_DO_DANGLING(pushDeletep(ifp), ifp);
            iterate(newIfp);
        } else if (guardp) {
            // No pattern variable but have guard - AND the conditions
            // guardp is already unlinked, use directly
            AstLogAnd* const combinedCondp = new AstLogAnd{fl, condp, guardp};
            combinedCondp->dtypeSetBit();
            ifp->condp(combinedCondp);
            // Iterate the modified if to transform any nested matches in guard
            iterate(ifp);
        } else {
            // No pattern variable, no guard - just use tag condition
            ifp->condp(condp);
            // Iterate in case there are matches expressions in the body
            iterate(ifp);
        }

        ++m_statTaggedMatches;
    }

    // Transform case matches statements
    void transformCaseMatches(AstCase* casep) {
        FileLine* const fl = casep->fileline();

        // Get the expression being matched
        AstNodeExpr* const exprp = casep->exprp();
        AstNodeDType* const exprDtp = exprp->dtypep()->skipRefp();
        AstUnionDType* const unionp = VN_CAST(exprDtp, UnionDType);

        if (!unionp || !unionp->isTagged()) {
            casep->v3error("Case matches expression must be a tagged union type");
            return;
        }

        const int tagWidth = unionp->tagBitWidth();
        const bool isUnpacked = !unionp->packed();

        // Create a variable to hold the expression (evaluate once)
        // For packed: use bit-packed variable
        // For unpacked: use the union dtype
        AstVar* tempVarp;
        if (isUnpacked) {
            // Use direct dtype - V3Width has already run so VFlagChildDType won't work
            tempVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtagged_expr", unionp};
        } else {
            const int totalWidth = unionp->taggedTotalWidth();
            tempVarp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vtagged_expr", VFlagBitPacked{},
                                  totalWidth};
        }
        tempVarp->funcLocal(true);

        // Assign expression to temp variable
        AstVarRef* const tempVarWrp = new AstVarRef{fl, tempVarp, VAccess::WRITE};
        AstAssign* const tempAssignp = new AstAssign{fl, tempVarWrp, exprp->cloneTree(false)};

        // Create tag extraction expression
        AstVarRef* const tempVarRd1p = new AstVarRef{fl, tempVarp, VAccess::READ};
        AstNodeExpr* tagExprp;
        if (isUnpacked) {
            tagExprp = makeTagExtractUnpacked(fl, tempVarRd1p);
        } else {
            tagExprp = makeTagExtract(fl, tempVarRd1p, unionp);
        }

        // Process each case item and convert to regular case
        AstNode* newCaseItemsp = nullptr;
        AstNode* varDeclsp = nullptr;

        for (AstCaseItem* itemp = casep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            if (itemp->isDefault()) {
                // Default case - just keep as is
                AstCaseItem* const newItemp = new AstCaseItem{
                    itemp->fileline(), nullptr,
                    itemp->stmtsp() ? itemp->stmtsp()->cloneTree(true) : nullptr};
                if (newCaseItemsp) {
                    newCaseItemsp->addNext(newItemp);
                } else {
                    newCaseItemsp = newItemp;
                }
                continue;
            }

            // Process tagged patterns (AstTaggedPattern or AstTaggedExpr)
            for (AstNode* condp = itemp->condsp(); condp; condp = condp->nextp()) {
                AstTaggedPattern* const tagPatternp = VN_CAST(condp, TaggedPattern);
                AstTaggedExpr* const tagExprCondp = VN_CAST(condp, TaggedExpr);
                if (!tagPatternp && !tagExprCondp) continue;

                const string& memberName
                    = tagPatternp ? tagPatternp->name() : tagExprCondp->name();
                AstMemberDType* const memberp = findMember(unionp, memberName);
                if (!memberp) {
                    condp->v3error("Tagged union member '" << memberName << "' not found");
                    continue;
                }

                const int tagIndex = memberp->tagIndex();
                const bool isVoid = isVoidDType(memberp->subDTypep());

                // Create case condition: tagIndex as constant
                // For unpacked: use 32-bit constant
                // For packed: use tag width
                AstConst* tagConstp;
                if (isUnpacked) {
                    tagConstp = makeConst(itemp->fileline(), tagIndex, 32);
                } else {
                    tagConstp = makeConst(itemp->fileline(), tagIndex, tagWidth);
                }

                // Handle pattern variable binding (only for AstTaggedPattern with inner pattern)
                AstNode* stmtsp = itemp->stmtsp() ? itemp->stmtsp()->cloneTree(true) : nullptr;

                AstNode* const innerPatternp = tagPatternp ? tagPatternp->patternp() : nullptr;
                if (innerPatternp && !VN_IS(innerPatternp, PatternStar)) {
                    AstPatternVar* const patVarp = VN_CAST(innerPatternp, PatternVar);
                    if (patVarp && !isVoid) {
                        const string& varName = patVarp->name();
                        const int memberWidth = memberp->width();

                        // Create local variable
                        // For unpacked: use actual member dtype
                        // For packed: use bit-packed type
                        AstVar* varp;
                        if (isUnpacked) {
                            // Use direct dtype - V3Width has already run so VFlagChildDType won't
                            // work
                            varp = new AstVar{condp->fileline(), VVarType::BLOCKTEMP, varName,
                                              memberp->subDTypep()};
                        } else {
                            varp = new AstVar{condp->fileline(), VVarType::BLOCKTEMP, varName,
                                              VFlagBitPacked{}, memberWidth};
                        }
                        varp->funcLocal(true);
                        if (varDeclsp) {
                            varDeclsp->addNext(varp);
                        } else {
                            varDeclsp = varp;
                        }

                        // Create assignment
                        // For unpacked: var = temp_expr.MemberName
                        // For packed: var = temp_expr[0 +: memberWidth]
                        AstVarRef* const tempVarRd2p = new AstVarRef{fl, tempVarp, VAccess::READ};
                        AstNodeExpr* dataExtractp;
                        if (isUnpacked) {
                            dataExtractp = makeDataExtractUnpacked(fl, tempVarRd2p, memberName,
                                                                   memberp->subDTypep());
                        } else {
                            dataExtractp = makeDataExtract(fl, tempVarRd2p, unionp, memberWidth);
                            if (dataExtractp) {
                                dataExtractp->dtypeSetBitSized(memberWidth, VSigning::UNSIGNED);
                            }
                        }
                        if (dataExtractp) {
                            AstVarRef* const varRefp
                                = new AstVarRef{condp->fileline(), varp, VAccess::WRITE};
                            AstAssign* const assignp = new AstAssign{fl, varRefp, dataExtractp};
                            // Replace pattern variable references in cloned statements
                            if (stmtsp) {
                                replacePatternVarRefs(stmtsp, varName, varp);
                                AstNode::addNext<AstNode, AstNode>(assignp, stmtsp);
                            }
                            stmtsp = assignp;
                        }
                    }
                }

                // Create new case item
                AstCaseItem* const newItemp
                    = new AstCaseItem{itemp->fileline(), tagConstp, stmtsp};
                if (newCaseItemsp) {
                    newCaseItemsp->addNext(newItemp);
                } else {
                    newCaseItemsp = newItemp;
                }
            }
        }

        // Create new case statement with tag extraction as expression
        AstCase* const newCasep
            = new AstCase{fl, VCaseType::CT_CASE, tagExprp, VN_AS(newCaseItemsp, CaseItem)};

        // Create C++ local scope with variable declarations, temp assign, and case
        AstCLocalScope* const scopep = new AstCLocalScope{fl, nullptr};
        scopep->addStmtsp(tempVarp);
        if (varDeclsp) scopep->addStmtsp(varDeclsp);
        scopep->addStmtsp(tempAssignp);
        scopep->addStmtsp(newCasep);

        // Replace original case
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
        UASSERT_OBJ(memberp, taggedp, "Member not found in tagged union");

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
        AstNodeDType* const dtypep = nodep->dtypep();
        if (!dtypep) {  // LCOV_EXCL_START  // V3Width catches this first
            nodep->v3warn(E_UNSUPPORTED, "Tagged expression without type context");
            return;
        }  // LCOV_EXCL_STOP
        AstUnionDType* const unionp = VN_CAST(dtypep->skipRefp(), UnionDType);
        if (!unionp || !unionp->isTagged()) {  // LCOV_EXCL_START  // V3Width catches this first
            nodep->v3error("Tagged expression used with non-tagged-union type");
            return;
        }  // LCOV_EXCL_STOP

        // For unpacked tagged unions, handle at assignment level
        // This includes explicitly unpacked unions and those with dynamic/array members
        if (!unionp->packed()) {
            // Find parent assignment
            AstAssign* assignp = VN_CAST(nodep->backp(), Assign);
            if (assignp && assignp->rhsp() == nodep) {
                transformTaggedExprUnpacked(assignp, nodep, unionp);
                ++m_statTaggedExprs;
                return;
            }
            // If not in simple assignment context, this is more complex
            // For now, emit an error for unsupported contexts
            nodep->v3warn(E_UNSUPPORTED,
                          "Tagged expression in non-simple assignment context");
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
