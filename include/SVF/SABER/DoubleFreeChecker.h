//===- DoubleFreeChecker.h -- Checking double-free errors---------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2017>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * DoubleFreeChecker.h
 *
 *  Created on: Apr 24, 2014
 *      Author: Yulei Sui
 */

#ifndef DOUBLEFREECHECKER_H_
#define DOUBLEFREECHECKER_H_

#include "SABER/LeakChecker.h"
#include "Util/Bug.h"

/*!
 * Double free checker to check deallocations of memory
 */

class DoubleFreeChecker : public LeakChecker {

public:
    typedef std::set<const LeakBug *> LeakBugSet;

    /// Pass ID
    static char ID;

    /// Constructor
    DoubleFreeChecker(char id = ID): LeakChecker(ID) {
    }

    /// Destructor
    virtual ~DoubleFreeChecker() {
        for (auto iter = bugs.begin(); iter != bugs.end(); iter++) {
            if (*iter != nullptr)
                delete *iter;
        }
    }

    /// We start from here
    virtual bool runOnModule(SVFModule module) {
        /// start analysis
        analyze(module);
        // / Write all bugs found to a report file;
        writeToReport();
        return false;
    }

    /// Get pass name
    virtual inline llvm::StringRef getPassName() const {
        return "Double Free Analysis";
    }

    /// Pass dependence
    virtual void getAnalysisUsage(llvm::AnalysisUsage& au) const {
        /// do not intend to change the IR in this pass,
        au.setPreservesAll();
    }

    // / Add bug to the set of all found bugs.
    // @{
    inline void
    addBug(const ProgSlice * slice)
    {
        const SVFGNode * src = slice->getSource();
        std::string fileName = svfgAnalysisUtil::getSVFGSourceFileName(src);
        std::string funcName = svfgAnalysisUtil::getSVFGFuncName(src);
        uint32_t sourceLine  = svfgAnalysisUtil::getSVFGSourceLine(src);

        DoubleFreeBug * bug = new DoubleFreeBug();

        bug->setLocation(fileName, funcName, sourceLine);
        bug->setDoubleFreePath(slice->evalFinalCond());

        bugs.insert(bug);
    }

    // @}

    // / Write the found bugs to a report file.
    void
    writeToReport();

    /// Report file/close bugs
    void reportBug(ProgSlice* slice);

private:
    LeakBugSet bugs;
};

#endif /* DOUBLEFREECHECKER_H_ */
