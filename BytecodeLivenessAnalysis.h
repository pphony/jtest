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

#ifndef BytecodeLivenessAnalysis_h
#define BytecodeLivenessAnalysis_h

#include "BytecodeBasicBlock.h"
#include <wtf/FastBitVector.h>
#include <wtf/HashMap.h>
#include <wtf/Vector.h>

// kt
#include <map>
#include <set>
#include "JSObject.h"

namespace JSC {

class CodeBlock;
class FullBytecodeLiveness;

  //kt
  typedef std::map<unsigned, unsigned> SymbolMap;
  typedef std::map<unsigned, std::set<unsigned> > SymbolMap2;
  typedef std::map<std::pair<bool, CString>, std::set<unsigned> > SymbolMap3;

class BytecodeLivenessAnalysis {
public:
    BytecodeLivenessAnalysis(CodeBlock*);
    
    bool operandIsLiveAtBytecodeOffset(int operand, unsigned bytecodeOffset);
    FastBitVector getLivenessInfoAtBytecodeOffset(unsigned bytecodeOffset);
    
    void computeFullLiveness(FullBytecodeLiveness& result);

    Vector<RefPtr<BytecodeBasicBlock> > m_basicBlocks;

    // kt for reaching def
    std::map<unsigned, FastBitVector> m_In;
    std::map<unsigned, FastBitVector> m_Out;
    std::map<unsigned, unsigned> m_Gen;
//    std::map<unsigned, std::pair<JSObject*, CString> > m_Prop;
    std::map<unsigned, std::pair<bool, CString> > m_GenString;
    std::map<unsigned, FastBitVector> m_Use;
    void getReachingInfoAtBytecodeOffset(unsigned , std::set<Instruction *>& );

private:
    void compute();
    void runLivenessFixpoint();
    void dumpResults();

    void getLivenessInfoForNonCapturedVarsAtBytecodeOffset(unsigned bytecodeOffset, FastBitVector&);
    
    // kt
    void dumpResults2();
    void reachingDef();
    void generateGenKill(SymbolMap2& kill);
    void computeLocalGen(CodeBlock* , BytecodeBasicBlock* , Vector<RefPtr<BytecodeBasicBlock> >& , SymbolMap2&, SymbolMap3& );
    void computeLocalKill(CodeBlock* , BytecodeBasicBlock* , Vector<RefPtr<BytecodeBasicBlock> >& , SymbolMap2& , SymbolMap2&,SymbolMap3& );
    void computeLocalReachingDefForBlock(CodeBlock* , BytecodeBasicBlock* , Vector<RefPtr<BytecodeBasicBlock> >& , SymbolMap2& );
void computeLocalReachingDefForBytecodeOffset(CodeBlock* , BytecodeBasicBlock* , Vector<RefPtr<BytecodeBasicBlock> >& , unsigned , FastBitVector& , SymbolMap2& );
void stepOverInstruction2(CodeBlock* , Vector<RefPtr<BytecodeBasicBlock>>& , unsigned , FastBitVector& , FastBitVector& , FastBitVector& , SymbolMap2& );

    CodeBlock* m_codeBlock;
};

inline bool operandIsAlwaysLive(CodeBlock*, int operand);
inline bool operandThatIsNotAlwaysLiveIsLive(CodeBlock*, const FastBitVector& out, int operand);
inline bool operandIsLive(CodeBlock*, const FastBitVector& out, int operand);

FastBitVector getLivenessInfo(CodeBlock*, const FastBitVector& out);

} // namespace JSC

#endif // BytecodeLivenessAnalysis_h
