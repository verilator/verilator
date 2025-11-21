#ifndef VERILATOR_V3LINKDOTIFACECAPTURE_H_
#define VERILATOR_V3LINKDOTIFACECAPTURE_H_

#include "config_build.h"

#include <functional>
#include <cstddef>

class AstCell;
class AstRefDType;
class VSymEnt;

namespace LinkDotIfaceCapture {

struct CapturedIfaceTypedef final {
    AstRefDType* refp = nullptr;
    AstCell* cellp = nullptr;
    VSymEnt* ownerSymp = nullptr;
};

void enable(bool flag);
bool enabled();

void reset();
void add(AstRefDType* refp, AstCell* cellp, VSymEnt* ownerSymp);
void add(const CapturedIfaceTypedef& entry);
bool contains(const AstRefDType* refp);
const CapturedIfaceTypedef* find(const AstRefDType* refp);
void forEach(const std::function<void(const CapturedIfaceTypedef&)>& fn);
bool replaceRef(const AstRefDType* oldRefp, AstRefDType* newRefp);
std::size_t size();

void propagateClone(const AstRefDType* origRefp, AstRefDType* newRefp);

}  // namespace LinkDotIfaceCapture

#endif  // VERILATOR_V3LINKDOTIFACECAPTURE_H_
