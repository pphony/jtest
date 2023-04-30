/*
 * Copyright (C) 2008, 2012, 2013 Apple Inc. All rights reserved.
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
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL APPLE INC. OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
 * OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. 
 */

#include "config.h"
#include "JITCode.h"

#include "LLIntThunks.h"
#include "JSCInlines.h"
#include "RegisterPreservationWrapperGenerator.h"
#include <wtf/PrintStream.h>

namespace JSC {

// kt
//extern std::map<std::pair<JSObject*, CString>, JSValue> shadow;
//extern std::set<std::pair<JSObject*, CString> > shadow_global2;
//extern std::map<JSValue, std::pair<JSObject*, CString> > shadow2;

extern std::list<Worklist> List;
extern std::list<Worklist>::iterator Iter;

  unsigned int Worklist::idCounter = 0;

  unsigned int JITcodeExecuteCounter = 0;

JITCode::JITCode(JITType jitType)
    : m_jitType(jitType)
{
}

JITCode::~JITCode()
{
}

// kt
void JITCode::dumpTime(struct timeval ts1, struct timeval ts2, PrintStream& out)
{
  struct timeval diff;
  timersub(&ts2, &ts1, &diff);
  out.printf("time spent: %ld.%06ld\n", diff.tv_sec, diff.tv_usec);
}

void JITCode::dumpSwitchedBranch(PrintStream& out)
{
		std::vector<ExecutedBranch>::iterator it = Iter->e.switchedBranch.begin();
		Iter->itCurExec = it;

    out.print("callToJavaScript(START) SWITCHED:\n");
    
    /*
	  */
		for (; it != Iter->e.switchedBranch.end(); it++)
		{
		  if (it->isCall())
        out.print("\t\tc count:", it->count, " addr:", it->addr, " hash:", it->hash,"\n");
      else
        out.print("\t\tb count:", it->count, " addr:", it->addr, " target:", it->target, " hash:", it->hash,"\n");
    }
}

void JITCode::dumpExecutedBranch(PrintStream& out)
{
		std::vector<ExecutedBranch>::iterator it = Iter->e.executedBranch.begin();

    out.print("callToJavaScript(END) EXECUTED:\n");
	  
		for (; it != Iter->e.executedBranch.end(); it++)
		{
		  if (it->isCall())
        out.print("\t\tc count:", it->count, " addr:", it->addr, " hash:", it->hash,"\n");
      else
        out.print("\t\tb count:", it->count, " addr:", it->addr, " target:", it->target, " hash:", it->hash,"\n");
    }
}

bool checkAlreadyExecuted(ProtoCallFrame* protoCallFrame)
{
  static std::set<unsigned> executedCodeBlocks;  // filter 

  CodeBlock *codeBlock = protoCallFrame->codeBlock();

  std::set<unsigned>::iterator it = executedCodeBlocks.find(codeBlock->hash().hash());
  if (it != executedCodeBlocks.end()) // already executed
    return false;

  executedCodeBlocks.insert(codeBlock->hash().hash());

  return true;
}

JSValue JITCode::execute(VM* vm, ProtoCallFrame* protoCallFrame)
{
// kt
//  static struct timeval ts1, ts2, ts3;
  unsigned int C = JITcodeExecuteCounter++;
  WTF::dataFile().print("JITCode::exec(START) ", C, " ",  protoCallFrame->codeBlock()->inferredName(), "#", protoCallFrame->codeBlock()->hashAsStringIfPossible(), "\n");
  

  // return if already executed
  if (!checkAlreadyExecuted(protoCallFrame))
  {
    WTF::dataFile().print("JITCode::exec(END) ", C, "(pass)\n");
    return jsNull() ;
  }


	Worklist w;	// current worklist

	List.push_front(w);
	Iter = List.begin();

	Iter->initWorklist();

//  vm->frameCount =0;
//  shadow.clear();   // shadow memory clear
//  shadow2.clear();   
//  shadow_global2.clear();   

    dumpSwitchedBranch();

//    if (JITcodeExecuteCounter == 1)
//      gettimeofday(&ts1, NULL);

    JSValue result = JSValue::decode(callToJavaScript(executableAddress(), vm, protoCallFrame));

//    if (JITcodeExecuteCounter == 1)
//    {
//      gettimeofday(&ts2, NULL);
//      dumpTime(ts1, ts2);
//    }

    dumpExecutedBranch();

	Iter->q.push(Iter->e);

	while ( !Iter->q.empty() )
	{
		Iter->popWorklist(Iter->e2);  // pop into e2

		for (std::vector<ExecutedBranch>::iterator it1 = Iter->e2.executedBranch.begin(); it1 != Iter->e2.executedBranch.end(); it1++)
		{
		  if (it1->isCall())
		      continue;
			for (std::set<unsigned int>::iterator it2 = Iter->branches[std::make_pair(it1->addr, it1->hash)].begin(); it2 != Iter->branches[std::make_pair(it1->addr, it1->hash)].end(); it2++)
			{
//			  unsigned hash = protoCallFrame->codeBlock()->hash().hash();
				ExecutedBranch t;

				if (it1->target == *it2)	// already executed
					continue;
				if (Iter->covered.find(std::make_pair(*it2, it1->hash)) != Iter->covered.end())	// already executed
					continue;

				Iter->count_idx =0;
//        Iter->frameDepth = 0;
        Iter->loopCount.clear();
				Iter->e.executedBranch.clear();
				Iter->e.switchedBranch.clear();

//				Iter->e.switchedBranch = Iter->e2.switchedBranch;   // old approach 
				for (std::vector<ExecutedBranch>::iterator iter = Iter->e2.executedBranch.begin(); iter->count < it1->count && iter != Iter->e2.executedBranch.end(); iter++)   // new approach to avoid state separation
				  Iter->e.switchedBranch.push_back(*iter);

				t.count = it1->count;
				t.addr = it1->addr;
				t.hash = it1->hash;
				t.target = *it2;
				Iter->e.switchedBranch.push_back(t);

//        shadow.clear();   // shadow memory clear
//        shadow2.clear();   
//        shadow_global2.clear();   


        dumpSwitchedBranch();

				callToJavaScript(executableAddress(), vm, protoCallFrame);

        dumpExecutedBranch();
				
				Iter->q.push(Iter->e);
			}
		}
	}


	List.pop_front();
//	if (!List.empty())
		Iter = List.begin();

//  gettimeofday(&ts3, NULL);   // final execution time
//  dumpTime(ts1, ts3);

  WTF::dataFile().print("JITCode::exec(END) ", C, "\n");
  if (vm->exception())
    WTF::dataFile().print("\tJITCODE EXCEPTION\n");
  if (result.isUndefinedOrNull())
    WTF::dataFile().print("\tJITCODE RESULT UNDEFINED\n");


    return vm->exception() ? jsNull() : result;
}

DFG::CommonData* JITCode::dfgCommon()
{
    RELEASE_ASSERT_NOT_REACHED();
    return 0;
}

DFG::JITCode* JITCode::dfg()
{
    RELEASE_ASSERT_NOT_REACHED();
    return 0;
}

FTL::JITCode* JITCode::ftl()
{
    RELEASE_ASSERT_NOT_REACHED();
    return 0;
}

FTL::ForOSREntryJITCode* JITCode::ftlForOSREntry()
{
    RELEASE_ASSERT_NOT_REACHED();
    return 0;
}

JITCodeWithCodeRef::JITCodeWithCodeRef(JITType jitType)
    : JITCode(jitType)
{
}

JITCodeWithCodeRef::JITCodeWithCodeRef(CodeRef ref, JITType jitType)
    : JITCode(jitType)
    , m_ref(ref)
{
}

JITCodeWithCodeRef::~JITCodeWithCodeRef()
{
}

void* JITCodeWithCodeRef::executableAddressAtOffset(size_t offset)
{
    RELEASE_ASSERT(m_ref);
    return reinterpret_cast<char*>(m_ref.code().executableAddress()) + offset;
}

void* JITCodeWithCodeRef::dataAddressAtOffset(size_t offset)
{
    RELEASE_ASSERT(m_ref);
    ASSERT(offset <= size()); // use <= instead of < because it is valid to ask for an address at the exclusive end of the code.
    return reinterpret_cast<char*>(m_ref.code().dataLocation()) + offset;
}

unsigned JITCodeWithCodeRef::offsetOf(void* pointerIntoCode)
{
    RELEASE_ASSERT(m_ref);
    intptr_t result = reinterpret_cast<intptr_t>(pointerIntoCode) - reinterpret_cast<intptr_t>(m_ref.code().executableAddress());
    ASSERT(static_cast<intptr_t>(static_cast<unsigned>(result)) == result);
    return static_cast<unsigned>(result);
}

size_t JITCodeWithCodeRef::size()
{
    RELEASE_ASSERT(m_ref);
    return m_ref.size();
}

bool JITCodeWithCodeRef::contains(void* address)
{
    RELEASE_ASSERT(m_ref);
    return m_ref.executableMemory()->contains(address);
}

DirectJITCode::DirectJITCode(JITType jitType)
    : JITCodeWithCodeRef(jitType)
{
}

DirectJITCode::DirectJITCode(JITCode::CodeRef ref, JITCode::CodePtr withArityCheck, JITType jitType)
    : JITCodeWithCodeRef(ref, jitType)
    , m_withArityCheck(withArityCheck)
{
}

DirectJITCode::~DirectJITCode()
{
}

void DirectJITCode::initializeCodeRef(JITCode::CodeRef ref, JITCode::CodePtr withArityCheck)
{
    RELEASE_ASSERT(!m_ref);
    m_ref = ref;
    m_withArityCheck = withArityCheck;
}

DirectJITCode::RegisterPreservationWrappers* DirectJITCode::ensureWrappers()
{
    if (!m_wrappers)
        m_wrappers = std::make_unique<RegisterPreservationWrappers>();
    return m_wrappers.get();
}

JITCode::CodePtr DirectJITCode::addressForCall(
    VM& vm, ExecutableBase* executable, ArityCheckMode arity,
    RegisterPreservationMode registers)
{
    switch (arity) {
    case ArityCheckNotRequired:
        switch (registers) {
        case RegisterPreservationNotRequired:
            RELEASE_ASSERT(m_ref);
            return m_ref.code();
        case MustPreserveRegisters: {
#if ENABLE(JIT)
            RegisterPreservationWrappers* wrappers = ensureWrappers();
            if (!wrappers->withoutArityCheck)
                wrappers->withoutArityCheck = generateRegisterPreservationWrapper(vm, executable, m_ref.code());
            return wrappers->withoutArityCheck.code();
#else
            UNUSED_PARAM(vm);
            UNUSED_PARAM(executable);
            RELEASE_ASSERT_NOT_REACHED();
#endif
        } }
    case MustCheckArity:
        switch (registers) {
        case RegisterPreservationNotRequired:
            RELEASE_ASSERT(m_withArityCheck);
            return m_withArityCheck;
        case MustPreserveRegisters: {
#if ENABLE(JIT)
            RegisterPreservationWrappers* wrappers = ensureWrappers();
            if (!wrappers->withArityCheck)
                wrappers->withArityCheck = generateRegisterPreservationWrapper(vm, executable, m_withArityCheck);
            return wrappers->withArityCheck.code();
#else
            RELEASE_ASSERT_NOT_REACHED();
#endif
        } }
    }
    RELEASE_ASSERT_NOT_REACHED();
    return CodePtr();
}

NativeJITCode::NativeJITCode(JITType jitType)
    : JITCodeWithCodeRef(jitType)
{
}

NativeJITCode::NativeJITCode(CodeRef ref, JITType jitType)
    : JITCodeWithCodeRef(ref, jitType)
{
}

NativeJITCode::~NativeJITCode()
{
}

void NativeJITCode::initializeCodeRef(CodeRef ref)
{
    ASSERT(!m_ref);
    m_ref = ref;
}

JITCode::CodePtr NativeJITCode::addressForCall(
    VM&, ExecutableBase*, ArityCheckMode, RegisterPreservationMode)
{
    RELEASE_ASSERT(!!m_ref);
    return m_ref.code();
}

} // namespace JSC

namespace WTF {

void printInternal(PrintStream& out, JSC::JITCode::JITType type)
{
    switch (type) {
    case JSC::JITCode::None:
        out.print("None");
        return;
    case JSC::JITCode::HostCallThunk:
        out.print("Host");
        return;
    case JSC::JITCode::InterpreterThunk:
        out.print("LLInt");
        return;
    case JSC::JITCode::BaselineJIT:
        out.print("Baseline");
        return;
    case JSC::JITCode::DFGJIT:
        out.print("DFG");
        return;
    case JSC::JITCode::FTLJIT:
        out.print("FTL");
        return;
    default:
        CRASH();
        return;
    }
}

} // namespace WTF

