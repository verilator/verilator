#pragma once

#include <array>
#include <fstream>
#include "../definitions.h"
#include "../util/random.h"

namespace whfc {
    class WHFC_IO {
    public:
        struct WHFCInformation {
            std::array<NodeWeight, 2> maxBlockWeight;
            Flow upperFlowBound;
            Node s, t;
        };

        static void readRandomGeneratorState(const std::string& hgpath, Randomizer& rng) {
            std::ifstream df(hgpath + ".distribution");
            if (df) {
                df >> rng.get64BitUintDistribution();
            }
            df.close();

            std::ifstream genf(hgpath + ".generator");
            if (genf) {
                genf >> rng.getGenerator();
            }
            genf.close();
        }

        static WHFCInformation readAdditionalInformation(const std::string& hgpath) {
            std::string fileSuffix = ".whfc";
            std::ifstream f(hgpath + fileSuffix);
            WHFCInformation i;
            f >> i.maxBlockWeight[0] >> i.maxBlockWeight[1] >> i.upperFlowBound >> i.s >> i.t;
            f.close();
            return i;
        }

        static void writeAdditionalInformation(std::string& hgpath, WHFCInformation& i, Randomizer& rng) {
            std::string fileSuffix = ".whfc";
            std::ofstream f(hgpath + fileSuffix);
            f << i.maxBlockWeight[0] << " " << i.maxBlockWeight[1] << " " << i.upperFlowBound << " " << i.s << " " << i.t << std::endl;
            f.close();

            std::ofstream df(hgpath + ".distribution");
            df << rng.get64BitUintDistribution();
            df.close();

            std::ofstream genf(hgpath + ".generator");
            genf << rng.getGenerator();
            genf.close();
        }
    };
} // namespace whfc
