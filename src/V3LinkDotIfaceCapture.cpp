
#include "V3LinkDotIfaceCapture.h"

#include "V3Ast.h"
#include "V3SymTable.h"

#include <unordered_map>

namespace {

using CapturedMap = std::unordered_map<const AstRefDType*, LinkDotIfaceCapture::CapturedIfaceTypedef>;

CapturedMap& capturedMap() {
    static CapturedMap s_map;
    return s_map;
}

}  // namespace

namespace LinkDotIfaceCapture {

void reset() { capturedMap().clear(); }

void add(AstRefDType* refp, AstCell* cellp, VSymEnt* ownerSymp) {
    if (!refp) return;
    capturedMap()[refp] = CapturedIfaceTypedef{refp, cellp, ownerSymp};
}

void add(const CapturedIfaceTypedef& entry) {
    if (!entry.refp) return;
    capturedMap()[entry.refp] = entry;
}

bool contains(const AstRefDType* refp) {
    if (!refp) return false;
    return capturedMap().find(refp) != capturedMap().end();
}

const CapturedIfaceTypedef* find(const AstRefDType* refp) {
    if (!refp) return nullptr;
    const auto it = capturedMap().find(refp);
    if (VL_UNLIKELY(it == capturedMap().end())) return nullptr;
    return &it->second;
}

void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn) {
    if (!fn) return;
    for (const auto& entry : capturedMap()) fn(entry.second);
}

bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp) {
    if (!oldRefp || !newRefp) return false;
    auto& map = capturedMap();
    const auto it = map.find(oldRefp);
    if (it == map.end()) return false;
    auto entry = it->second;
    entry.refp = newRefp;
    map.erase(it);
    map.emplace(newRefp, entry);
    return true;
}

std::size_t size() { return capturedMap().size(); }

}  // namespace LinkDotIfaceCapture
