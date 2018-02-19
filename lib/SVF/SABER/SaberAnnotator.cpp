//===- SaberAnnotator.cpp -- Annotation---------------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2016>  <Yulei Sui>
// Copyright (C) <2013-2016>  <Jingling Xue>

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
 * SaberAnnotator.cpp
 *
 *  Created on: May 4, 2014
 *      Author: Yulei Sui
 */

#include "SABER/SaberAnnotator.h"
#include "SABER/ProgSlice.h"
#include "Util/DebugUtil.h"

using namespace llvm;

/*!
 * Adds some information to the metadata of a source instruction.
 */
//void SaberAnnotator::annotateSource() {
//	std::string str;
//	raw_string_ostream rawstr(str);
//	rawstr << SB_SLICESOURCE ; //<< _curSlice->getSource()->getId();
//
//	if(const StmtSVFGNode* stmt = dyn_cast<StmtSVFGNode>(_curSlice->getSource())) {
//		if(const Instruction* sourceinst = stmt->getInst()) {
//			my_addMDTag(const_cast<Instruction*>(sourceinst),rawstr.str());
//		}
//		else {
//			assert(false && "instruction of source node not found");
//		}
//	}
//	else
//		assert(false && "instruction of source node not found");
//
//}
//
//void SaberAnnotator::annotateSinks() {
//	for(ProgSlice::SVFGNodeSet::iterator it = _curSlice->getSinks().begin(),
//			eit = _curSlice->getSinks().end(); it!=eit; ++it) {
//
//		if(const StmtSVFGNode* stmt = dyn_cast<StmtSVFGNode>(*it)) {
//			if(const Instruction* sinkinst = stmt->getInst()) {
//				std::string str;
//				raw_string_ostream rawstr(str);
//				rawstr << SB_SLICESINK << (*it)->getId();
//				my_addMDTag(const_cast<Instruction*>(sinkinst),rawstr.str());
//			}
//			else {
//				assert(false && "instruction of source node not found");
//			}
//		}
//		else
//			assert(false && "instruction of source node not found");
//	}
//}

/*!
 * Adds some information to the metadata of a source instruction.
 */
void SaberAnnotator::annotateSource() {
	std::string str;
	raw_string_ostream rawstr(str);
	rawstr << SB_SLICESOURCE ; //<< _curSlice->getSource()->getId();

	if(const Value* v = _curSlice->getLLVMValue(_curSlice->getSource())) {
		if(const Instruction* sourceinst = dyn_cast<Instruction>(v)) 
			addMDTag(const_cast<Instruction*>(sourceinst),rawstr.str());
		else 
			assert(false && "instruction of source node not found");
	}
	else
		assert(false && "instruction of source node not found");

}

/*!
 * Adds some information to the metadata of a sink instruction.
 */
void SaberAnnotator::annotateSinks() {
	for(ProgSlice::SVFGNodeSet::iterator it = _curSlice->getSinks().begin(),
			eit = _curSlice->getSinks().end(); it!=eit; ++it) {
		if(const ActualParmSVFGNode* ap = dyn_cast<ActualParmSVFGNode>(*it)) {
			const Instruction* sinkinst = ap->getCallSite().getInstruction();
			assert(isa<CallInst>(sinkinst) && "not a call instruction?");
			const CallInst* sink = cast<CallInst>(sinkinst);
			std::string str;
			raw_string_ostream rawstr(str);
			rawstr << SB_SLICESINK << _curSlice->getSource()->getId();
			addMDTag(const_cast<CallInst*>(sink),sink->getArgOperand(0),rawstr.str());
		}
		else
			assert(false && "sink node is not a actual parameter?");
	}
}

/*!
 * Annotate branch instruction and its corresponding feasible path
 */
void SaberAnnotator::annotateFeasibleBranch(const BranchInst *brInst, u32_t succPos) {

	assert((succPos == 0 || succPos == 1) && "branch instruction should only have two successors");

	std::string str;
	raw_string_ostream rawstr(str);
	rawstr << SB_FESIBLE << _curSlice->getSource()->getId();
	BranchInst* br = const_cast<BranchInst*>(brInst);
	addMDTag(br,br->getCondition(),rawstr.str());
}

/*!
 * Annotate branch instruction and its corresponding infeasible path
 */
void SaberAnnotator::annotateInfeasibleBranch(const BranchInst *brInst, u32_t succPos) {

	assert((succPos == 0 || succPos == 1) && "branch instruction should only have two successors");

	std::string str;
	raw_string_ostream rawstr(str);
	rawstr << SB_INFESIBLE << _curSlice->getSource()->getId();
	BranchInst* br = const_cast<BranchInst*>(brInst);
	addMDTag(br,br->getCondition(),rawstr.str());
}


/*!
 * Annotate switch instruction and its corresponding feasible path
 */
void SaberAnnotator::annotateSwitch(SwitchInst *switchInst, u32_t succPos) {
	assert(succPos < switchInst->getNumSuccessors() && "successor position not correct!");
}




