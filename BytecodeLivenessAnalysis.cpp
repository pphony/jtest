/*
 * Copyright (C) 2013 Apple Inc. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. AND ITS CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL APPLE INC. OR ITS CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "config.h"
#include "BytecodeLivenessAnalysis.h"

#include "BytecodeLivenessAnalysisInlines.h"
#include "BytecodeUseDef.h"
#include "CodeBlock.h"
#include "FullBytecodeLiveness.h"
#include "PreciseJumpTargets.h"

namespace JSC {

  //kt
  typedef std::map<unsigned, unsigned> SymbolMap;
  typedef std::map<unsigned, unsigned >::iterator SymbolMapIter;
  typedef std::map<unsigned, std::set<unsigned> > SymbolMap2;
  typedef std::map<unsigned, std::set<unsigned> >::iterator SymbolMap2Iter;
  typedef std::map<std::pair<bool, CString>, std::set<unsigned> > SymbolMap3;
  typedef std::map<std::pair<bool, CString>, std::set<unsigned> >::iterator SymbolMap3Iter;

BytecodeLivenessAnalysis::BytecodeLivenessAnalysis(CodeBlock* codeBlock)
    : m_codeBlock(codeBlock)
{
    ASSERT(m_codeBlock);
    compute();
}

static bool isValidRegisterForLiveness(CodeBlock* codeBlock, int operand)
{
    if (codeBlock->isConstantRegisterIndex(operand))
        return false;
    
    VirtualRegister virtualReg(operand);
    if (!virtualReg.isLocal())
        return false;
    
    if (codeBlock->captureCount()
        && operand <= codeBlock->captureStart()
        && operand > codeBlock->captureEnd())
        return false;
    
    return true;
}

static void setForOperand(CodeBlock* codeBlock, FastBitVector& bits, int operand)
{
    ASSERT(isValidRegisterForLiveness(codeBlock, operand));
    VirtualRegister virtualReg(operand);
    if (virtualReg.offset() > codeBlock->captureStart())
        bits.set(virtualReg.toLocal());
    else
        bits.set(virtualReg.toLocal() - codeBlock->captureCount());
}

namespace {

class SetBit {
public:
    SetBit(FastBitVector& bits)
        : m_bits(bits)
    {
    }
    
    void operator()(CodeBlock* codeBlock, Instruction*, OpcodeID, int operand)
    {
        if (isValidRegisterForLiveness(codeBlock, operand))
            setForOperand(codeBlock, m_bits, operand);
    }
    
private:
    FastBitVector& m_bits;
};

} // anonymous namespace

static unsigned getLeaderOffsetForBasicBlock(RefPtr<BytecodeBasicBlock>* basicBlock)
{
    return (*basicBlock)->leaderBytecodeOffset();
}

static BytecodeBasicBlock* findBasicBlockWithLeaderOffset(Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, unsigned leaderOffset)
{
    return (*tryBinarySearch<RefPtr<BytecodeBasicBlock>, unsigned>(basicBlocks, basicBlocks.size(), leaderOffset, getLeaderOffsetForBasicBlock)).get();
}

static bool blockContainsBytecodeOffset(BytecodeBasicBlock* block, unsigned bytecodeOffset)
{
    unsigned leaderOffset = block->leaderBytecodeOffset();
    return bytecodeOffset >= leaderOffset && bytecodeOffset < leaderOffset + block->totalBytecodeLength();
}

static BytecodeBasicBlock* findBasicBlockForBytecodeOffset(Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, unsigned bytecodeOffset)
{
/*
    for (unsigned i = 0; i < basicBlocks.size(); i++) {
        if (blockContainsBytecodeOffset(basicBlocks[i].get(), bytecodeOffset))
            return basicBlocks[i].get();
    }
    return 0;
*/
    RefPtr<BytecodeBasicBlock>* basicBlock = approximateBinarySearch<RefPtr<BytecodeBasicBlock>, unsigned>(
        basicBlocks, basicBlocks.size(), bytecodeOffset, getLeaderOffsetForBasicBlock);
    // We found the block we were looking for.
    if (blockContainsBytecodeOffset((*basicBlock).get(), bytecodeOffset))
        return (*basicBlock).get();

    // Basic block is to the left of the returned block.
    if (bytecodeOffset < (*basicBlock)->leaderBytecodeOffset()) {
        ASSERT(basicBlock - 1 >= basicBlocks.data());
        ASSERT(blockContainsBytecodeOffset(basicBlock[-1].get(), bytecodeOffset));
        return basicBlock[-1].get();
    }

    // Basic block is to the right of the returned block.
    ASSERT(&basicBlock[1] <= &basicBlocks.last());
    ASSERT(blockContainsBytecodeOffset(basicBlock[1].get(), bytecodeOffset));
    return basicBlock[1].get();
}

static void stepOverInstruction(CodeBlock* codeBlock, Vector<RefPtr<BytecodeBasicBlock>>& basicBlocks, unsigned bytecodeOffset, FastBitVector& uses, FastBitVector& defs, FastBitVector& out)
{
    uses.clearAll();
    defs.clearAll();
    
    SetBit setUses(uses);
    SetBit setDefs(defs);
    computeUsesForBytecodeOffset(codeBlock, bytecodeOffset, setUses);
    computeDefsForBytecodeOffset(codeBlock, bytecodeOffset, setDefs);
    
    out.exclude(defs);
    out.merge(uses);
    
    // If we have an exception handler, we want the live-in variables of the 
    // exception handler block to be included in the live-in of this particular bytecode.
    if (HandlerInfo* handler = codeBlock->handlerForBytecodeOffset(bytecodeOffset)) {
        BytecodeBasicBlock* handlerBlock = findBasicBlockWithLeaderOffset(basicBlocks, handler->target);
        ASSERT(handlerBlock);
        out.merge(handlerBlock->in());
    }
}

static void computeLocalLivenessForBytecodeOffset(CodeBlock* codeBlock, BytecodeBasicBlock* block, Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, unsigned targetOffset, FastBitVector& result)
{
    ASSERT(!block->isExitBlock());
    ASSERT(!block->isEntryBlock());

    FastBitVector out = block->out();

    FastBitVector uses;
    FastBitVector defs;
    uses.resize(out.numBits());
    defs.resize(out.numBits());

    for (int i = block->bytecodeOffsets().size() - 1; i >= 0; i--) {
        unsigned bytecodeOffset = block->bytecodeOffsets()[i];
        if (targetOffset > bytecodeOffset)
            break;
        
        stepOverInstruction(codeBlock, basicBlocks, bytecodeOffset, uses, defs, out);
    }

    result.set(out);
}

static void computeLocalLivenessForBlock(CodeBlock* codeBlock, BytecodeBasicBlock* block, Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks)
{
    if (block->isExitBlock() || block->isEntryBlock())
        return;
    computeLocalLivenessForBytecodeOffset(codeBlock, block, basicBlocks, block->leaderBytecodeOffset(), block->in());
}

void BytecodeLivenessAnalysis::runLivenessFixpoint()
{
    UnlinkedCodeBlock* unlinkedCodeBlock = m_codeBlock->unlinkedCodeBlock();
    unsigned numberOfVariables =
        unlinkedCodeBlock->m_numCalleeRegisters - m_codeBlock->captureCount();

    for (unsigned i = 0; i < m_basicBlocks.size(); i++) {
        BytecodeBasicBlock* block = m_basicBlocks[i].get();
        block->in().resize(numberOfVariables);
        block->out().resize(numberOfVariables);
    }

    bool changed;
    m_basicBlocks.last()->in().clearAll();
    m_basicBlocks.last()->out().clearAll();
    FastBitVector newOut;
    newOut.resize(m_basicBlocks.last()->out().numBits());
    do {
        changed = false;
        for (int i = m_basicBlocks.size() - 2; i >= 0; i--) {
            BytecodeBasicBlock* block = m_basicBlocks[i].get();
            newOut.clearAll();
            for (unsigned j = 0; j < block->successors().size(); j++)
                newOut.merge(block->successors()[j]->in());
            bool outDidChange = block->out().setAndCheck(newOut);
            computeLocalLivenessForBlock(m_codeBlock, block, m_basicBlocks);
            changed |= outDidChange;
        }
    } while (changed);
}

void BytecodeLivenessAnalysis::getLivenessInfoForNonCapturedVarsAtBytecodeOffset(unsigned bytecodeOffset, FastBitVector& result)
{
    BytecodeBasicBlock* block = findBasicBlockForBytecodeOffset(m_basicBlocks, bytecodeOffset);
    ASSERT(block);
    ASSERT(!block->isEntryBlock());
    ASSERT(!block->isExitBlock());
    result.resize(block->out().numBits());
    computeLocalLivenessForBytecodeOffset(m_codeBlock, block, m_basicBlocks, bytecodeOffset, result);
}

bool BytecodeLivenessAnalysis::operandIsLiveAtBytecodeOffset(int operand, unsigned bytecodeOffset)
{
    if (operandIsAlwaysLive(m_codeBlock, operand))
        return true;
    FastBitVector result;
    getLivenessInfoForNonCapturedVarsAtBytecodeOffset(bytecodeOffset, result);
    return operandThatIsNotAlwaysLiveIsLive(m_codeBlock, result, operand);
}

FastBitVector getLivenessInfo(CodeBlock* codeBlock, const FastBitVector& out)
{
    FastBitVector result;

    unsigned numCapturedVars = codeBlock->captureCount();
    if (numCapturedVars) {
        int firstCapturedLocal = VirtualRegister(codeBlock->captureStart()).toLocal();
        result.resize(out.numBits() + numCapturedVars);
        for (unsigned i = 0; i < numCapturedVars; ++i)
            result.set(firstCapturedLocal + i);
    } else
        result.resize(out.numBits());

    int outLength = out.numBits();
    ASSERT(outLength >= 0);
    for (int i = 0; i < outLength; i++) {
        if (!out.get(i))
            continue;

        if (!numCapturedVars) {
            result.set(i);
            continue;
        }

        if (virtualRegisterForLocal(i).offset() > codeBlock->captureStart())
            result.set(i);
        else 
            result.set(numCapturedVars + i);
    }
    return result;
}

FastBitVector BytecodeLivenessAnalysis::getLivenessInfoAtBytecodeOffset(unsigned bytecodeOffset)
{
    FastBitVector out;
    getLivenessInfoForNonCapturedVarsAtBytecodeOffset(bytecodeOffset, out);
    return getLivenessInfo(m_codeBlock, out);
}

void BytecodeLivenessAnalysis::computeFullLiveness(FullBytecodeLiveness& result)
{
    FastBitVector out;
    FastBitVector uses;
    FastBitVector defs;
    
    result.m_codeBlock = m_codeBlock;
    result.m_map.clear();
    
    for (unsigned i = m_basicBlocks.size(); i--;) {
        BytecodeBasicBlock* block = m_basicBlocks[i].get();
        if (block->isEntryBlock() || block->isExitBlock())
            continue;
        
        out = block->out();
        uses.resize(out.numBits());
        defs.resize(out.numBits());
        
        for (unsigned i = block->bytecodeOffsets().size(); i--;) {
            unsigned bytecodeOffset = block->bytecodeOffsets()[i];
            stepOverInstruction(m_codeBlock, m_basicBlocks, bytecodeOffset, uses, defs, out);
            result.m_map.add(bytecodeOffset, out);
        }
    }
}

void BytecodeLivenessAnalysis::dumpResults()
{
    Interpreter* interpreter = m_codeBlock->vm()->interpreter;
    Instruction* instructionsBegin = m_codeBlock->instructions().begin();
    for (unsigned i = 0; i < m_basicBlocks.size(); i++) {
        BytecodeBasicBlock* block = m_basicBlocks[i].get();
        dataLogF("\nBytecode basic block %u: %p (offset: %u, length: %u)\n", i, block, block->leaderBytecodeOffset(), block->totalBytecodeLength());
        dataLogF("Predecessors: ");
        for (unsigned j = 0; j < block->predecessors().size(); j++) {
            BytecodeBasicBlock* predecessor = block->predecessors()[j];
            dataLogF("%p ", predecessor);
        }
        dataLogF("\n");
        dataLogF("Successors: ");
        for (unsigned j = 0; j < block->successors().size(); j++) {
            BytecodeBasicBlock* successor = block->successors()[j];
            dataLogF("%p ", successor);
        }
        dataLogF("\n");
        if (block->isEntryBlock()) {
            dataLogF("Entry block %p\n", block);
            continue;
        }
        if (block->isExitBlock()) {
            dataLogF("Exit block: %p\n", block);
            continue;
        }
        for (unsigned bytecodeOffset = block->leaderBytecodeOffset(); bytecodeOffset < block->leaderBytecodeOffset() + block->totalBytecodeLength();) {
            const Instruction* currentInstruction = &instructionsBegin[bytecodeOffset];

            dataLogF("Live variables: ");
            FastBitVector liveBefore = getLivenessInfoAtBytecodeOffset(bytecodeOffset);
            for (unsigned j = 0; j < liveBefore.numBits(); j++) {
                if (liveBefore.get(j))
                    dataLogF("%u ", j);
            }
            dataLogF("\n");
            m_codeBlock->dumpBytecode(WTF::dataFile(), m_codeBlock->globalObject()->globalExec(), instructionsBegin, currentInstruction);

            OpcodeID opcodeID = interpreter->getOpcodeID(instructionsBegin[bytecodeOffset].u.opcode);
            unsigned opcodeLength = opcodeLengths[opcodeID];
            bytecodeOffset += opcodeLength;
        }

        dataLogF("Live variables: ");
        FastBitVector liveAfter = block->out();
        for (unsigned j = 0; j < liveAfter.numBits(); j++) {
            if (liveAfter.get(j))
                dataLogF("%u ", j);
        }
        dataLogF("\n");
    }
}

void BytecodeLivenessAnalysis::compute()
{
    computeBytecodeBasicBlocks(m_codeBlock, m_basicBlocks);
    ASSERT(m_basicBlocks.size());
//    runLivenessFixpoint();

    // kt
//    reachingDef();
//    dumpResults2();

//    if (Options::dumpBytecodeLivenessResults())
//        dumpResults();
}

// kt
// following functions are written by kt
void BytecodeLivenessAnalysis::getReachingInfoAtBytecodeOffset(unsigned bytecodeOffset, std::set<Instruction *>& instructions)
{
    Instruction* instructionsBegin = m_codeBlock->instructions().begin();
    Instruction* current = &instructionsBegin[bytecodeOffset];
    Interpreter* interpreter = m_codeBlock->vm()->interpreter;
    int use;
    OpcodeID opcodeID = interpreter->getOpcodeID(current->u.opcode);
    switch (opcodeID) {
      case op_put_to_scope:   // ??
      case op_put_by_id:
      case op_put_by_id_out_of_line:
      case op_put_by_id_transition_direct:
      case op_put_by_id_transition_direct_out_of_line:
      case op_put_by_id_transition_normal:
      case op_put_by_id_transition_normal_out_of_line:
        use = current[1].u.operand;
        break;
      default:
        use = current[2].u.operand;
    }

    std::map<unsigned, FastBitVector>::iterator it = m_In.find(bytecodeOffset);
    if (it != m_In.end())
    {
      FastBitVector in = it->second;
      for (unsigned j = 0; j < in.numBits(); j++) 
      {
        if (in.get(j))
        {
          Instruction *candidate = &instructionsBegin[j];
          if (use == candidate[1].u.operand)
          {
            OpcodeID opcodeID = interpreter->getOpcodeID(candidate->u.opcode);
            switch (opcodeID) {
              case op_put_to_scope:
              case op_put_by_id:
              case op_put_by_id_out_of_line:
              case op_put_by_id_transition_direct:
              case op_put_by_id_transition_direct_out_of_line:
              case op_put_by_id_transition_normal:
              case op_put_by_id_transition_normal_out_of_line:
                {
                  // To Do
                }
                break;
              default:
                instructions.insert(candidate);
            }
          }
        }
      }
    }
}

void BytecodeLivenessAnalysis::dumpResults2()
{
    Interpreter* interpreter = m_codeBlock->vm()->interpreter;
    Instruction* instructionsBegin = m_codeBlock->instructions().begin();
    for (unsigned i = 0; i < m_basicBlocks.size(); i++) {
        BytecodeBasicBlock* block = m_basicBlocks[i].get();
        dataLogF("\nBytecode basic block %u: %p (offset: %u, length: %u)\n", i, block, block->leaderBytecodeOffset(), block->totalBytecodeLength());
        dataLogF("Predecessors: ");
        for (unsigned j = 0; j < block->predecessors().size(); j++) {
            BytecodeBasicBlock* predecessor = block->predecessors()[j];
            dataLogF("%p ", predecessor);
        }
        dataLogF("\n");
        dataLogF("Successors: ");
        for (unsigned j = 0; j < block->successors().size(); j++) {
            BytecodeBasicBlock* successor = block->successors()[j];
            dataLogF("%p ", successor);
        }
        dataLogF("\n");
        if (block->isEntryBlock()) {
            dataLogF("Entry block %p\n", block);
            continue;
        }
        if (block->isExitBlock()) {
            dataLogF("Exit block: %p\n", block);
            continue;
        }
        for (unsigned bytecodeOffset = block->leaderBytecodeOffset(); bytecodeOffset < block->leaderBytecodeOffset() + block->totalBytecodeLength();) 
        {
            const Instruction* currentInstruction = &instructionsBegin[bytecodeOffset];

          dataLogF("Reaching Definition: ");
          dataLogF("In: ");
          std::map<unsigned, FastBitVector>::iterator it = m_In.find(bytecodeOffset);
          if (it != m_In.end())
          {
            FastBitVector in = it->second;
            for (unsigned j = 0; j < in.numBits(); j++) {
                if (in.get(j))
                    dataLogF("%u ", j);
            }
          }

          dataLogF("Out: ");
          std::map<unsigned, FastBitVector>::iterator it2 = m_Out.find(bytecodeOffset);
          if (it2 != m_Out.end())
          {
            FastBitVector out = it2->second;
            for (unsigned j = 0; j < out.numBits(); j++) {
                if (out.get(j))
                    dataLogF("%u ", j);
            }
          }

            dataLogF("\n");
            m_codeBlock->dumpBytecode(WTF::dataFile(), m_codeBlock->globalObject()->globalExec(), instructionsBegin, currentInstruction);

          std::map<unsigned, unsigned>::iterator it3 = m_Gen.find(bytecodeOffset);
          if (it3 != m_Gen.end())
          {
            dataLogF("Gen: %u ", it3->second);
            dataLogF("\n");
          }
          else 
          {
            OpcodeID opcodeID = interpreter->getOpcodeID(instructionsBegin[bytecodeOffset].u.opcode);
            switch (opcodeID) {
            case op_put_to_scope:
            case op_put_by_id:
            case op_put_by_id_out_of_line:
            case op_put_by_id_transition_direct:
            case op_put_by_id_transition_direct_out_of_line:
            case op_put_by_id_transition_normal:
            case op_put_by_id_transition_normal_out_of_line:
              {
                    std::map<unsigned, std::pair<bool, CString> >::iterator it4 = m_GenString.find(bytecodeOffset);
                    if (it4 != m_GenString.end())
                    {
                      dataLogF("Gen: %s ", it4->second.second.data());
                      dataLogF("\n");
                    }
              }
              break;
            default:;
            }
          }

          dataLogF("Use: ");
          std::map<unsigned, FastBitVector>::iterator it4 = m_Use.find(bytecodeOffset);
          if (it4 != m_Use.end())
          {
            FastBitVector out = it4->second;
            for (unsigned j = 0; j < out.numBits(); j++) {
                if (out.get(j))
                    dataLogF("%u ", j);
            }
          }
            dataLogF("\n");

            OpcodeID opcodeID = interpreter->getOpcodeID(instructionsBegin[bytecodeOffset].u.opcode);
            unsigned opcodeLength = opcodeLengths[opcodeID];
            bytecodeOffset += opcodeLength;
        }

        dataLogF("\n");
    }
}

void BytecodeLivenessAnalysis::stepOverInstruction2(CodeBlock* codeBlock, Vector<RefPtr<BytecodeBasicBlock>>& basicBlocks, unsigned bytecodeOffset, FastBitVector& gens, FastBitVector& kills, FastBitVector& in, SymbolMap2& kill)
{
    gens.clearAll();
    kills.clearAll();

    // update "in" in BytecodeLivenessAnalysis
    m_In[bytecodeOffset] = in;
    
    // remove kills from in
    SymbolMap2Iter it = kill.find(bytecodeOffset);
    if (it != kill.end())
    {
      std::set<unsigned>::iterator it2 = it->second.begin(); 
      for (; it2 != it->second.end(); ++it2)
        kills.set(*it2);
      
      in.exclude(kills);
    }

    // add gens to in
    SymbolMapIter it2 = m_Gen.find(bytecodeOffset);
    if (it2 != m_Gen.end())
    {
      gens.set(bytecodeOffset);
      in.merge(gens);
    }
    else
    {
      std::map<unsigned, std::pair<bool, CString> >::iterator it3 = m_GenString.find(bytecodeOffset);
      if (it3 != m_GenString.end())
      {
        gens.set(bytecodeOffset);
        in.merge(gens);
      }
    }

    // update "out" in BytecodeLivenessAnalysis
    m_Out[bytecodeOffset] = in;
    
    // If we have an exception handler, we want the live-in variables of the 
    // exception handler block to be included in the live-in of this particular bytecode.
//    if (HandlerInfo* handler = codeBlock->handlerForBytecodeOffset(bytecodeOffset)) {
//        BytecodeBasicBlock* handlerBlock = findBasicBlockWithLeaderOffset(basicBlocks, handler->target);
//        ASSERT(handlerBlock);
//        in.merge(handlerBlock->in());
//    }
}

void BytecodeLivenessAnalysis::computeLocalReachingDefForBytecodeOffset(CodeBlock* codeBlock, BytecodeBasicBlock* block, Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, unsigned targetOffset, FastBitVector& result, SymbolMap2& kill)
{
    ASSERT(!block->isExitBlock());
    ASSERT(!block->isEntryBlock());

    FastBitVector in = block->in2();

    FastBitVector gens;
    FastBitVector kills;
    gens.resize(in.numBits());
    kills.resize(in.numBits());


    for (unsigned i = 0; i < block->bytecodeOffsets().size(); i++) {
      unsigned bytecodeOffset = block->bytecodeOffsets()[i];
      if (targetOffset <= bytecodeOffset)
        break;
        
        stepOverInstruction2(codeBlock, basicBlocks, bytecodeOffset, gens, kills, in, kill);
    }

    result.set(in);
}

void BytecodeLivenessAnalysis::computeLocalReachingDefForBlock(CodeBlock* codeBlock, BytecodeBasicBlock* block, Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, SymbolMap2& kill)
{
  if (block->isExitBlock() || block->isEntryBlock())
      return;
  computeLocalReachingDefForBytecodeOffset(codeBlock, block, basicBlocks, block->leaderBytecodeOffset() + block->totalBytecodeLength(), block->out2(), kill);
}

void BytecodeLivenessAnalysis::computeLocalKill(CodeBlock* codeBlock, BytecodeBasicBlock* block, Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, SymbolMap2& kill, SymbolMap2& map, SymbolMap3& map_prop)
{
  if (block->isExitBlock() || block->isEntryBlock())
      return;

  for (unsigned j = 0; j < block->bytecodeOffsets().size(); j++) 
  {
    unsigned bytecodeOffset = block->bytecodeOffsets()[j];

    Instruction* instructionsBegin = codeBlock->instructions().begin();
    OpcodeID opcodeID = codeBlock->vm()->interpreter->getOpcodeID(instructionsBegin[bytecodeOffset].u.opcode);
    switch (opcodeID) {
    // put_to_scope/put_by_id
    case op_put_to_scope:
      {
          std::map<unsigned, std::pair<bool, CString> >::iterator it4 = m_GenString.find(bytecodeOffset);
          if (it4 != m_GenString.end())
          {
            if (it4->second.first == true)
            {
              SymbolMap3Iter it5 = map_prop.find(it4->second);
              if (it5 != map_prop.end())
                for (std::set<unsigned>::iterator i = it5->second.begin(); i != it5->second.end(); i++)
                  kill[bytecodeOffset].insert(*i);
            }
          }
      }
      break;
    case op_put_by_id:
    case op_put_by_id_out_of_line:
    case op_put_by_id_transition_direct:
    case op_put_by_id_transition_direct_out_of_line:
    case op_put_by_id_transition_normal:
    case op_put_by_id_transition_normal_out_of_line:
      {
          std::map<unsigned, std::pair<bool, CString> >::iterator it4 = m_GenString.find(bytecodeOffset);
          if (it4 != m_GenString.end())
          {
            if (it4->second.first == false)
            {
              SymbolMap3Iter it5 = map_prop.find(it4->second);
              if (it5 != map_prop.end())
                for (std::set<unsigned>::iterator i = it5->second.begin(); i != it5->second.end(); i++)
                  kill[bytecodeOffset].insert(*i);
            }
          }
      }
      break;
    default:
      {
        SymbolMapIter it = m_Gen.find(bytecodeOffset);
        if (it == m_Gen.end())
          continue;

        SymbolMap2Iter it2 = map.find(it->second);
        if (it2 == map.end())
          continue;

        for (std::set<unsigned>::iterator i = it2->second.begin(); i != it2->second.end(); i++)
          kill[bytecodeOffset].insert(*i);
      }

    }
    
  }
}

void BytecodeLivenessAnalysis::computeLocalGen(CodeBlock* codeBlock, BytecodeBasicBlock* block, Vector<RefPtr<BytecodeBasicBlock> >& basicBlocks, SymbolMap2& map, SymbolMap3& map_prop)
{
  if (block->isExitBlock() || block->isEntryBlock())
      return;

  UnlinkedCodeBlock* unlinkedCodeBlock = codeBlock->unlinkedCodeBlock();
  unsigned numberOfVariables = unlinkedCodeBlock->m_numCalleeRegisters - codeBlock->captureCount();

  FastBitVector gens;
  FastBitVector uses;
  gens.resize(numberOfVariables);
  uses.resize(numberOfVariables);

  for (unsigned j = 0; j < block->bytecodeOffsets().size(); j++) 
  {
    int k;
    unsigned bytecodeOffset = block->bytecodeOffsets()[j];

    gens.clearAll();
    uses.clearAll();

    SetBit setGens(gens);
    SetBit setUses(uses);
    computeDefsForBytecodeOffset(codeBlock, bytecodeOffset, setGens);
    computeUsesForBytecodeOffset(codeBlock, bytecodeOffset, setUses);

    // put_to_scope setting
    Instruction* instructionsBegin = codeBlock->instructions().begin();
    Instruction* instruction = &instructionsBegin[bytecodeOffset];
    OpcodeID opcodeID = codeBlock->vm()->interpreter->getOpcodeID(instruction->u.opcode);
    switch (opcodeID) {
    case op_put_to_scope:
      {
      Identifier ident = codeBlock->identifier(instruction[2].u.operand);
//      JSObject* scope = jsCast<JSObject*>(ExecState::uncheckedR(instruction[1].u.operand).jsValue());
      m_GenString[bytecodeOffset] = std::make_pair(true, ident.utf8());
      map_prop[std::make_pair(true, ident.utf8())].insert(bytecodeOffset);
      }
      break;
    case op_put_by_id:
    case op_put_by_id_out_of_line:
    case op_put_by_id_transition_direct:
    case op_put_by_id_transition_direct_out_of_line:
    case op_put_by_id_transition_normal:
    case op_put_by_id_transition_normal_out_of_line:
//    case op_put_getter_setter:
//    case op_put_by_val:
//    case op_put_by_val_direct:
//    case op_put_by_index:
      {
      Identifier ident = codeBlock->identifier(instruction[2].u.operand);
      m_GenString[bytecodeOffset] = std::make_pair(false, ident.utf8());
      map_prop[std::make_pair(false, ident.utf8())].insert(bytecodeOffset);
      }
      break;
    default:
      ;
    }

    // for debugging
    m_Use[bytecodeOffset] = uses;

    for (k = gens.numBits()-1; k>=0; k--)
      if (gens.get(k))
        break;

    if (k<0)
      continue;

    m_Gen[bytecodeOffset] = k;

    map[k].insert(bytecodeOffset);
  }
}

void BytecodeLivenessAnalysis::generateGenKill(SymbolMap2& kill)
{
  SymbolMap2 map;
  SymbolMap3 map_prop;

  // gen
  for (unsigned i = 1; i < m_basicBlocks.size(); i++) 
  {
    BytecodeBasicBlock* block = m_basicBlocks[i].get();
    computeLocalGen(m_codeBlock, block, m_basicBlocks, map, map_prop);
  }

  //kill
  for (unsigned i = 1; i < m_basicBlocks.size(); i++) 
  {
    BytecodeBasicBlock* block = m_basicBlocks[i].get();
    computeLocalKill(m_codeBlock, block, m_basicBlocks, kill, map, map_prop);
  }
}

void BytecodeLivenessAnalysis::reachingDef()
{
  unsigned numberOfInstructions = m_codeBlock->instructions().size();
//  SymbolMap gen;
  SymbolMap2 kill;

  generateGenKill(kill);

  for (unsigned i = 0; i < m_basicBlocks.size(); i++) {
    BytecodeBasicBlock* block = m_basicBlocks[i].get();
    block->in2().resize(numberOfInstructions);
    block->out2().resize(numberOfInstructions);
  }

  bool changed;
  m_basicBlocks.first()->in2().clearAll();
  m_basicBlocks.first()->out2().clearAll();
  FastBitVector newIn;  // for merging incoming edges
  newIn.resize(m_basicBlocks.first()->in2().numBits());
  do {
      changed = false;
      for (unsigned i = 1; i < m_basicBlocks.size(); i++) {  // from second block to exit block
          BytecodeBasicBlock* block = m_basicBlocks[i].get();
          newIn.clearAll();
          for (unsigned j = 0; j < block->predecessors().size(); j++)
              newIn.merge(block->predecessors()[j]->out2());
          bool inDidChange = block->in2().setAndCheck(newIn); // copy newIn to in2, and comparing "newIn" with original "in2"
          computeLocalReachingDefForBlock(m_codeBlock, block, m_basicBlocks, kill);
          changed |= inDidChange;
      }
  } while (changed);
}

} // namespace JSC
