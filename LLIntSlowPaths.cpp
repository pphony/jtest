/*
 * Copyright (C) 2011, 2012, 2013, 2014 Apple Inc. All rights reserved.
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
#include "LLIntSlowPaths.h"
#include "Arguments.h"
#include "ArrayConstructor.h"
#include "CallFrame.h"
#include "CommonSlowPaths.h"
#include "CommonSlowPathsExceptions.h"
#include "ErrorHandlingScope.h"
#include "GetterSetter.h"
#include "HostCallReturnValue.h"
#include "Interpreter.h"
#include "JIT.h"
#include "JITExceptions.h"
#include "JSActivation.h"
#include "JSCJSValue.h"
#include "JSGlobalObjectFunctions.h"
#include "JSNameScope.h"
#include "JSPropertyNameIterator.h"
#include "JSStackInlines.h"
#include "JSString.h"
#include "JSWithScope.h"
#include "LLIntCommon.h"
#include "LLIntExceptions.h"
#include "LowLevelInterpreter.h"
#include "ObjectConstructor.h"
#include "JSCInlines.h"
#include "ProtoCallFrame.h"
#include "StructureRareDataInlines.h"
#include <wtf/StringPrintStream.h>

// kt
#include "CodeBlock.h"

namespace JSC { 

// kt
//extern  std::set<std::pair<JSObject*, CString> > shadow_global2;
//extern  std::map<JSValue, std::pair<JSObject*, CString> > shadow2;

////extern std::map<std::pair<JSObject*, CString>, String> shadow_object;
extern std::list<Worklist> List;
extern std::list<Worklist>::iterator Iter;
static int count;
static int exceptionCount;

class UnwindFunctor;

namespace LLInt {

#define LOOPCOUNT 80000

// kt
#define INFINITE_LOOP(opcode) do {                      \
        std::map<std::pair<unsigned int, unsigned>, unsigned int>::iterator it = Iter->loopCount.find(std::make_pair(location,hash));\
			  if (it == Iter->loopCount.end()) {\
         /* WTF::dataFile().print("\tloopCount: 1\n");*/\
			    Iter->loopCount[std::make_pair(location, hash)] = 1;\
			  }\
			  else {\
			    if (it->second >= LOOPCOUNT ) {\
            WTF::dataFile().print("\tloopCount: ", LOOPCOUNT, "(overflow)\n");\
				    pc += OPCODE_LENGTH(opcode);                         \
				    Iter->updateBranchTarget(location, fallthru, exec->codeBlock());\
            LLINT_END_IMPL();                                         \
				  }\
			    Iter->loopCount[std::make_pair(location, hash)] = it->second +1;\
         /* WTF::dataFile().print("\tloopCount: ", it->second+1, "\n");*/\
			  } \
    } while (false)


#define LLINT_BEGIN_NO_SET_PC() \
    VM& vm = exec->vm();      \
    NativeCallFrameTracer tracer(&vm, exec)

#ifndef NDEBUG
#define LLINT_SET_PC_FOR_STUBS() do { \
        exec->codeBlock()->bytecodeOffset(pc); \
        exec->setCurrentVPC(pc + 1); \
    } while (false)
#else
#define LLINT_SET_PC_FOR_STUBS() do { \
        exec->setCurrentVPC(pc + 1); \
    } while (false)
#endif

#define LLINT_BEGIN()                           \
    LLINT_BEGIN_NO_SET_PC();                    \
    LLINT_SET_PC_FOR_STUBS()

#define LLINT_OP(index) (exec->uncheckedR(pc[index].u.operand))
#define LLINT_OP_C(index) (exec->r(pc[index].u.operand))

#define LLINT_RETURN_TWO(first, second) do {       \
        return encodeResult(first, second);        \
    } while (false)

#define LLINT_END_IMPL() LLINT_RETURN_TWO(pc, 0)

#define LLINT_THROW(exceptionToThrow) do {                        \
        vm.throwException(exec, exceptionToThrow);                \
        pc = returnToThrow(exec);                                 \
        LLINT_END_IMPL();                                         \
    } while (false)

#define LLINT_CHECK_EXCEPTION() do {                    \
        if (UNLIKELY(vm.exception())) {                 \
            pc = returnToThrow(exec);                   \
            LLINT_END_IMPL();                           \
        }                                               \
    } while (false)

#define LLINT_END() do {                        \
        LLINT_CHECK_EXCEPTION();                \
        LLINT_END_IMPL();                       \
    } while (false)

#define LLINT_BRANCH(opcode, condition) do {                      \
        bool __b_condition = (condition);                         \
        LLINT_CHECK_EXCEPTION();                                  \
        if (__b_condition)                                        \
            pc += pc[OPCODE_LENGTH(opcode) - 1].u.operand;        \
        else                                                      \
            pc += OPCODE_LENGTH(opcode);                          \
        LLINT_END_IMPL();                                         \
    } while (false)

// kt
#define LLINT_BRANCH2(opcode, condition) do {                      \
	Instruction *begin = exec->codeBlock()->instructions().begin();\
	unsigned int location = pc - begin;				\
        bool __b_condition = (condition);                         \
/*WTF::dataFile().print("(", location, ") ##opcode\n"); */ \
	Iter->count_idx++;						\
	CodeBlock *codeBlock = exec->codeBlock(); \
	unsigned hash = codeBlock->hash().hash();				\
        LLINT_CHECK_EXCEPTION();                                  \
	unsigned int taken = (pc + pc[OPCODE_LENGTH(opcode) - 1].u.operand) - begin;\
	unsigned int fallthru = (pc + OPCODE_LENGTH(opcode)) - begin;\
		if (Iter->itCurExec == Iter->e.switchedBranch.end())\
		{\
			if (__b_condition)                                        \
			{\
			  int offset = pc[OPCODE_LENGTH(opcode) - 1].u.operand;\
	      if (Iter->isRegisteredBranch(location, hash)) 	 {\
			    if (offset<0) {\
			      INFINITE_LOOP(opcode);\
			    }\
				  Iter->updateBranchTarget(location, taken, codeBlock);\
				}\
				else\
			      Iter->newBranch(location, taken, fallthru, codeBlock);\
				  pc += offset;       \
			}\
			else {\
	      if (Iter->isRegisteredBranch(location, hash)) 	 \
				  Iter->updateBranchTarget(location, fallthru, codeBlock);\
				else\
			    Iter->newBranch(location, fallthru, taken, codeBlock);\
				  pc += OPCODE_LENGTH(opcode);                         \
			}\
		}\
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)	{\
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);\
			pc = begin + Iter->itCurExec->target;\
			Iter->itCurExec++;\
		}\
		else{  \
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);\
		    Iter->itCurExec = Iter->e.switchedBranch.end();\
			  if (__b_condition)                                         {\
				  Iter->updateBranchTarget(location, taken, codeBlock);\
				  pc += pc[OPCODE_LENGTH(opcode) - 1].u.operand;       \
			  }\
			  else {\
				  Iter->updateBranchTarget(location, fallthru, codeBlock);\
				  pc += OPCODE_LENGTH(opcode);                         \
			  }\
		}\
        LLINT_END_IMPL();                                         \
    } while (false)

#define LLINT_RETURN(value) do {                \
        JSValue __r_returnValue = (value);      \
        LLINT_CHECK_EXCEPTION();                \
        LLINT_OP(1) = __r_returnValue;          \
        LLINT_END_IMPL();                       \
    } while (false)

#define LLINT_RETURN_WITH_PC_ADJUSTMENT(value, pcAdjustment) do { \
        JSValue __r_returnValue = (value);      \
        LLINT_CHECK_EXCEPTION();                \
        LLINT_OP(1) = __r_returnValue;          \
        pc += (pcAdjustment);                   \
        LLINT_END_IMPL();                       \
    } while (false)

#define LLINT_RETURN_PROFILED(opcode, value) do {               \
        JSValue __rp_returnValue = (value);                     \
        LLINT_CHECK_EXCEPTION();                                \
        LLINT_OP(1) = __rp_returnValue;                         \
        LLINT_PROFILE_VALUE(opcode, __rp_returnValue);          \
        LLINT_END_IMPL();                                       \
    } while (false)

#define LLINT_PROFILE_VALUE(opcode, value) do { \
        pc[OPCODE_LENGTH(opcode) - 1].u.profile->m_buckets[0] = \
        JSValue::encode(value);                  \
    } while (false)

#define LLINT_CALL_END_IMPL(exec, callTarget) LLINT_RETURN_TWO((callTarget), (exec))

#define LLINT_CALL_THROW(exec, exceptionToThrow) do {                   \
        ExecState* __ct_exec = (exec);                                  \
        vm.throwException(__ct_exec, exceptionToThrow);                 \
        LLINT_CALL_END_IMPL(0, callToThrow(__ct_exec));                 \
    } while (false)

#define LLINT_CALL_CHECK_EXCEPTION(exec) do {                           \
        ExecState* __cce_exec = (exec);                                 \
        if (UNLIKELY(vm.exception()))                                   \
            LLINT_CALL_END_IMPL(0, callToThrow(__cce_exec));            \
    } while (false)

#define LLINT_CALL_RETURN(exec, callTarget) do {                        \
        ExecState* __cr_exec = (exec);                                  \
        void* __cr_callTarget = (callTarget);                           \
        LLINT_CALL_CHECK_EXCEPTION(__cr_exec);                          \
        LLINT_CALL_END_IMPL(__cr_exec, __cr_callTarget);                \
    } while (false)

#define LLINT_RETURN_CALLEE_FRAME(execCallee) do {                      \
        ExecState* __rcf_exec = (execCallee);                           \
        LLINT_RETURN_TWO(pc, __rcf_exec);                               \
    } while (false)
    
#define CONSTRUCTOR() do {\
	    /* construct .. setupCall*/ \
	    ExecState* execCallee = exec - exec->codeBlock()->m_numCalleeRegisters -7;  \
	    execCallee->setArgumentCountIncludingThis(1); \
	    execCallee->uncheckedR(JSStack::Callee) = calleeAsValue;  \
	    execCallee->setCallerFrame(exec); \
      \
	    /* construct ... handleHostCall */ \
	    execCallee->setScope(exec->scope());  \
	    execCallee->setCodeBlock(0);  \
	    execCallee->clearReturnPC();  \
      \
	    ConstructData constructData;  \
	    ConstructType constructType = getConstructData(calleeAsValue, constructData); \
      \
	    if (constructType == ConstructTypeHost) { \
		    NativeCallFrameTracer tracer(&(exec->vm()), execCallee);  \
		    execCallee->setCallee(asObject(calleeAsValue)); \
		    exec->vm().hostCallReturnValue = JSValue::decode(constructData.native.function(execCallee));  \
	    } \
      /* result = slot.getValue(exec, ident);*/\
	    baseValue = exec->vm().hostCallReturnValue; \
    } while (false)


extern "C" SlowPathReturnType llint_trace_operand(ExecState* exec, Instruction* pc, int fromWhere, int operand)
{
    LLINT_BEGIN();
    dataLogF("%p / %p: executing bc#%zu, op#%u: Trace(%d): %d: %d\n",
            exec->codeBlock(),
            exec,
            static_cast<intptr_t>(pc - exec->codeBlock()->instructions().begin()),
            exec->vm().interpreter->getOpcodeID(pc[0].u.opcode),
            fromWhere,
            operand,
            pc[operand].u.operand);
    LLINT_END();
}

extern "C" SlowPathReturnType llint_trace_value(ExecState* exec, Instruction* pc, int fromWhere, int operand)
{
    JSValue value = LLINT_OP_C(operand).jsValue();
    union {
        struct {
            uint32_t tag;
            uint32_t payload;
        } bits;
        EncodedJSValue asValue;
    } u;
    u.asValue = JSValue::encode(value);
    dataLogF(
        "%p / %p: executing bc#%zu, op#%u: Trace(%d): %d: %d: %08x:%08x: %s\n",
        exec->codeBlock(),
        exec,
        static_cast<intptr_t>(pc - exec->codeBlock()->instructions().begin()),
        exec->vm().interpreter->getOpcodeID(pc[0].u.opcode),
        fromWhere,
        operand,
        pc[operand].u.operand,
        u.bits.tag,
        u.bits.payload,
        toCString(value).data());
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(trace_prologue)
{
    dataLogF("%p / %p: in prologue.\n", exec->codeBlock(), exec);
    LLINT_END_IMPL();
}

static void traceFunctionPrologue(ExecState* exec, const char* comment, CodeSpecializationKind kind)
{
    JSFunction* callee = jsCast<JSFunction*>(exec->callee());
    FunctionExecutable* executable = callee->jsExecutable();
    CodeBlock* codeBlock = executable->codeBlockFor(kind);
    dataLogF("%p / %p: in %s of function %p, executable %p; numVars = %u, numParameters = %u, numCalleeRegisters = %u, caller = %p.\n",
            codeBlock, exec, comment, callee, executable,
            codeBlock->m_numVars, codeBlock->numParameters(), codeBlock->m_numCalleeRegisters,
            exec->callerFrame());
}

LLINT_SLOW_PATH_DECL(trace_prologue_function_for_call)
{
    traceFunctionPrologue(exec, "call prologue", CodeForCall);
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(trace_prologue_function_for_construct)
{
    traceFunctionPrologue(exec, "construct prologue", CodeForConstruct);
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(trace_arityCheck_for_call)
{
    traceFunctionPrologue(exec, "call arity check", CodeForCall);
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(trace_arityCheck_for_construct)
{
    traceFunctionPrologue(exec, "construct arity check", CodeForConstruct);
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(trace)
{
    dataLogF("%p / %p: executing bc#%zu, %s, scope %p, pc = %p\n",
            exec->codeBlock(),
            exec,
            static_cast<intptr_t>(pc - exec->codeBlock()->instructions().begin()),
            opcodeNames[exec->vm().interpreter->getOpcodeID(pc[0].u.opcode)],
            exec->scope(), pc);
    if (exec->vm().interpreter->getOpcodeID(pc[0].u.opcode) == op_enter) {
        dataLogF("Frame will eventually return to %p\n", exec->returnPC().value());
        *bitwise_cast<volatile char*>(exec->returnPC().value());
    }
    if (exec->vm().interpreter->getOpcodeID(pc[0].u.opcode) == op_ret) {
        dataLogF("Will be returning to %p\n", exec->returnPC().value());
        dataLogF("The new cfr will be %p\n", exec->callerFrame());
    }
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(special_trace)
{
    dataLogF("%p / %p: executing special case bc#%zu, op#%u, return PC is %p\n",
            exec->codeBlock(),
            exec,
            static_cast<intptr_t>(pc - exec->codeBlock()->instructions().begin()),
            exec->vm().interpreter->getOpcodeID(pc[0].u.opcode),
            exec->returnPC().value());
    LLINT_END_IMPL();
}

enum EntryKind { Prologue, ArityCheck };

#if ENABLE(JIT)
inline bool shouldJIT(ExecState* exec)
{
    // You can modify this to turn off JITting without rebuilding the world.
    return exec->vm().canUseJIT();
}

// Returns true if we should try to OSR.
inline bool jitCompileAndSetHeuristics(CodeBlock* codeBlock, ExecState* exec)
{
    VM& vm = exec->vm();
    DeferGCForAWhile deferGC(vm.heap); // My callers don't set top callframe, so we don't want to GC here at all.
    
    codeBlock->updateAllValueProfilePredictions();
    
    if (!codeBlock->checkIfJITThresholdReached()) {
        if (Options::verboseOSR())
            dataLogF("    JIT threshold should be lifted.\n");
        return false;
    }
    
    switch (codeBlock->jitType()) {
    case JITCode::BaselineJIT: {
        if (Options::verboseOSR())
            dataLogF("    Code was already compiled.\n");
        codeBlock->jitSoon();
        return true;
    }
    case JITCode::InterpreterThunk: {
        CompilationResult result = JIT::compile(&vm, codeBlock, JITCompilationCanFail);
        switch (result) {
        case CompilationFailed:
            if (Options::verboseOSR())
                dataLogF("    JIT compilation failed.\n");
            codeBlock->dontJITAnytimeSoon();
            return false;
        case CompilationSuccessful:
            if (Options::verboseOSR())
                dataLogF("    JIT compilation successful.\n");
            codeBlock->install();
            codeBlock->jitSoon();
            return true;
        default:
            RELEASE_ASSERT_NOT_REACHED();
            return false;
        }
    }
    default:
        RELEASE_ASSERT_NOT_REACHED();
        return false;
    }
}

static SlowPathReturnType entryOSR(ExecState* exec, Instruction*, CodeBlock* codeBlock, const char *name, EntryKind kind)
{
    if (Options::verboseOSR()) {
        dataLog(
            *codeBlock, ": Entered ", name, " with executeCounter = ",
            codeBlock->llintExecuteCounter(), "\n");
    }
    
    if (!shouldJIT(exec)) {
        codeBlock->dontJITAnytimeSoon();
        LLINT_RETURN_TWO(0, 0);
    }
    if (!jitCompileAndSetHeuristics(codeBlock, exec))
        LLINT_RETURN_TWO(0, 0);
    
    if (kind == Prologue)
        LLINT_RETURN_TWO(codeBlock->jitCode()->executableAddress(), 0);
    ASSERT(kind == ArityCheck);
    LLINT_RETURN_TWO(codeBlock->jitCode()->addressForCall(
        *codeBlock->vm(), codeBlock->ownerExecutable(), MustCheckArity,
        RegisterPreservationNotRequired).executableAddress(), 0);
}
#else // ENABLE(JIT)
static SlowPathReturnType entryOSR(ExecState* exec, Instruction*, CodeBlock* codeBlock, const char*, EntryKind)
{
    codeBlock->dontJITAnytimeSoon();
    LLINT_RETURN_TWO(0, exec);
}
#endif // ENABLE(JIT)

LLINT_SLOW_PATH_DECL(entry_osr)
{
    return entryOSR(exec, pc, exec->codeBlock(), "entry_osr", Prologue);
}

LLINT_SLOW_PATH_DECL(entry_osr_function_for_call)
{
    return entryOSR(exec, pc, jsCast<JSFunction*>(exec->callee())->jsExecutable()->codeBlockForCall(), "entry_osr_function_for_call", Prologue);
}

LLINT_SLOW_PATH_DECL(entry_osr_function_for_construct)
{
    return entryOSR(exec, pc, jsCast<JSFunction*>(exec->callee())->jsExecutable()->codeBlockForConstruct(), "entry_osr_function_for_construct", Prologue);
}

LLINT_SLOW_PATH_DECL(entry_osr_function_for_call_arityCheck)
{
    return entryOSR(exec, pc, jsCast<JSFunction*>(exec->callee())->jsExecutable()->codeBlockForCall(), "entry_osr_function_for_call_arityCheck", ArityCheck);
}

LLINT_SLOW_PATH_DECL(entry_osr_function_for_construct_arityCheck)
{
    return entryOSR(exec, pc, jsCast<JSFunction*>(exec->callee())->jsExecutable()->codeBlockForConstruct(), "entry_osr_function_for_construct_arityCheck", ArityCheck);
}

LLINT_SLOW_PATH_DECL(loop_osr)
{
    CodeBlock* codeBlock = exec->codeBlock();

#if ENABLE(JIT)
    if (Options::verboseOSR()) {
        dataLog(
            *codeBlock, ": Entered loop_osr with executeCounter = ",
            codeBlock->llintExecuteCounter(), "\n");
    }
    
    if (!shouldJIT(exec)) {
        codeBlock->dontJITAnytimeSoon();
        LLINT_RETURN_TWO(0, 0);
    }
    
    if (!jitCompileAndSetHeuristics(codeBlock, exec))
        LLINT_RETURN_TWO(0, 0);
    
    ASSERT(codeBlock->jitType() == JITCode::BaselineJIT);
    
    Vector<BytecodeAndMachineOffset> map;
    codeBlock->jitCodeMap()->decode(map);
    BytecodeAndMachineOffset* mapping = binarySearch<BytecodeAndMachineOffset, unsigned>(map, map.size(), pc - codeBlock->instructions().begin(), BytecodeAndMachineOffset::getBytecodeIndex);
    ASSERT(mapping);
    ASSERT(mapping->m_bytecodeIndex == static_cast<unsigned>(pc - codeBlock->instructions().begin()));
    
    void* jumpTarget = codeBlock->jitCode()->executableAddressAtOffset(mapping->m_machineCodeOffset);
    ASSERT(jumpTarget);
    
    LLINT_RETURN_TWO(jumpTarget, exec->topOfFrame());
#else // ENABLE(JIT)
    UNUSED_PARAM(pc);
    codeBlock->dontJITAnytimeSoon();
    LLINT_RETURN_TWO(0, 0);
#endif // ENABLE(JIT)
}

LLINT_SLOW_PATH_DECL(replace)
{
    CodeBlock* codeBlock = exec->codeBlock();

#if ENABLE(JIT)
    if (Options::verboseOSR()) {
        dataLog(
            *codeBlock, ": Entered replace with executeCounter = ",
            codeBlock->llintExecuteCounter(), "\n");
    }
    
    if (shouldJIT(exec))
        jitCompileAndSetHeuristics(codeBlock, exec);
    else
        codeBlock->dontJITAnytimeSoon();
    LLINT_END_IMPL();
#else // ENABLE(JIT)
    codeBlock->dontJITAnytimeSoon();
    LLINT_END_IMPL();
#endif // ENABLE(JIT)
}

LLINT_SLOW_PATH_DECL(stack_check)
{
    LLINT_BEGIN();
#if LLINT_SLOW_PATH_TRACING
    dataLogF("Checking stack height with exec = %p.\n", exec);
    dataLogF("CodeBlock = %p.\n", exec->codeBlock());
    dataLogF("Num callee registers = %u.\n", exec->codeBlock()->m_numCalleeRegisters);
    dataLogF("Num vars = %u.\n", exec->codeBlock()->m_numVars);

#if ENABLE(LLINT_C_LOOP)
    dataLogF("Current end is at %p.\n", exec->vm().jsStackLimit());
#else
    dataLogF("Current end is at %p.\n", exec->vm().stackLimit());
#endif

#endif
    // This stack check is done in the prologue for a function call, and the
    // CallFrame is not completely set up yet. For example, if the frame needs
    // an activation object, the activation object will only be set up after
    // we start executing the function. If we need to throw a StackOverflowError
    // here, then we need to tell the prologue to start the stack unwinding from
    // the caller frame (which is fully set up) instead. To do that, we return
    // the caller's CallFrame in the second return value.
    //
    // If the stack check succeeds and we don't need to throw the error, then
    // we'll return 0 instead. The prologue will check for a non-zero value
    // when determining whether to set the callFrame or not.

    // For JIT enabled builds which uses the C stack, the stack is not growable.
    // Hence, if we get here, then we know a stack overflow is imminent. So, just
    // throw the StackOverflowError unconditionally.
#if !ENABLE(JIT)
    ASSERT(!vm.interpreter->stack().containsAddress(exec->topOfFrame()));
    if (LIKELY(vm.interpreter->stack().ensureCapacityFor(exec->topOfFrame())))
        LLINT_RETURN_TWO(pc, 0);
#endif

    exec = exec->callerFrame();
    vm.topCallFrame = exec;
    ErrorHandlingScope errorScope(vm);
    CommonSlowPaths::interpreterThrowInCaller(exec, createStackOverflowError(exec));
    pc = returnToThrowForThrownException(exec);
    LLINT_RETURN_TWO(pc, exec);
}

LLINT_SLOW_PATH_DECL(slow_path_create_activation)
{
    LLINT_BEGIN();
#if LLINT_SLOW_PATH_TRACING
    dataLogF("Creating an activation, exec = %p!\n", exec);
#endif
    JSActivation* activation = JSActivation::create(vm, exec, exec->codeBlock());
    exec->setScope(activation);
    LLINT_RETURN(JSValue(activation));
}

LLINT_SLOW_PATH_DECL(slow_path_new_object)
{
    LLINT_BEGIN();
    LLINT_RETURN(constructEmptyObject(exec, pc[3].u.objectAllocationProfile->structure()));
}

LLINT_SLOW_PATH_DECL(slow_path_new_array)
{
    LLINT_BEGIN();
    LLINT_RETURN(constructArrayNegativeIndexed(exec, pc[4].u.arrayAllocationProfile, bitwise_cast<JSValue*>(&LLINT_OP(2)), pc[3].u.operand));
}

LLINT_SLOW_PATH_DECL(slow_path_new_array_with_size)
{
    LLINT_BEGIN();
    LLINT_RETURN(constructArrayWithSizeQuirk(exec, pc[3].u.arrayAllocationProfile, exec->lexicalGlobalObject(), LLINT_OP_C(2).jsValue()));
}

LLINT_SLOW_PATH_DECL(slow_path_new_array_buffer)
{
    LLINT_BEGIN();
    LLINT_RETURN(constructArray(exec, pc[4].u.arrayAllocationProfile, exec->codeBlock()->constantBuffer(pc[2].u.operand), pc[3].u.operand));
}

LLINT_SLOW_PATH_DECL(slow_path_new_regexp)
{
    LLINT_BEGIN();
    RegExp* regExp = exec->codeBlock()->regexp(pc[2].u.operand);
    if (!regExp->isValid())
        LLINT_THROW(createSyntaxError(exec, "Invalid flag supplied to RegExp constructor."));
    LLINT_RETURN(RegExpObject::create(vm, exec->lexicalGlobalObject()->regExpStructure(), regExp));
}

LLINT_SLOW_PATH_DECL(slow_path_check_has_instance)
{
    LLINT_BEGIN();
    
    JSValue value = LLINT_OP_C(2).jsValue();
    JSValue baseVal = LLINT_OP_C(3).jsValue();
    if (baseVal.isObject()) {
        JSObject* baseObject = asObject(baseVal);
        ASSERT(!baseObject->structure()->typeInfo().implementsDefaultHasInstance());
        if (baseObject->structure()->typeInfo().implementsHasInstance()) {
            JSValue result = jsBoolean(baseObject->methodTable()->customHasInstance(baseObject, exec, value));
            LLINT_RETURN_WITH_PC_ADJUSTMENT(result, pc[4].u.operand);
        }
    }
    LLINT_THROW(createInvalidParameterError(exec, "instanceof", baseVal));
}

LLINT_SLOW_PATH_DECL(slow_path_instanceof)
{
    LLINT_BEGIN();
    JSValue value = LLINT_OP_C(2).jsValue();
    JSValue proto = LLINT_OP_C(3).jsValue();
    ASSERT(!value.isObject() || !proto.isObject());
    LLINT_RETURN(jsBoolean(JSObject::defaultHasInstance(exec, value, proto)));
}

LLINT_SLOW_PATH_DECL(slow_path_get_by_id)
{
    LLINT_BEGIN();

//	Instruction *begin = exec->codeBlock()->instructions().begin();
//	unsigned int location = pc - begin;				
//WTF::dataFile().print("(", location, ") get_by_id\n");

    CodeBlock* codeBlock = exec->codeBlock();
    const Identifier& ident = codeBlock->identifier(pc[3].u.operand);
    JSValue baseValue = LLINT_OP_C(2).jsValue();
//    PropertySlot slot(baseValue);

  // kt attempt 1 (gg)
//  if (baseValue.isUndefined())
//  {
//	  Identifier id(exec, "XMLHttpRequest");	// default: "XMLHttpRequest"
//	  if (codeBlock->lastGetFromScope.length() != 0)
//	  {
//		  std::map<Identifier, Info>::iterator it = codeBlock->ktMap.find(codeBlock->lastGetFromScope);	
//		  if (it != codeBlock->ktMap.end())
//			  id = it->second.id;
//	  }
//
//	  PropertySlot slot2(temp);
//    	  temp->getPropertySlot(exec, id, slot2);
//	  JSValue calleeAsValue = slot2.getValue(exec, id);
//
//    CONSTRUCTOR();
//
//  //	exec[-2] = baseValue;	
//	  LLINT_OP(2) = baseValue;	
//  }

  // kt new attempt (assign magic object)
  if (baseValue.isUndefinedOrNull())
  {
	  Identifier id(exec, "chrome");	 

    // get_from_scope ("chrome")
	  PropertySlot slot2(codeBlock->globalObject());
    codeBlock->globalObject()->getPropertySlot(exec, id, slot2);
	  JSValue chrome = slot2.getValue(exec, id);

    // finding object
	  Instruction *begin = codeBlock->instructions().begin();
	  unsigned int location = pc - begin;				
    std::set<Instruction *> insts;
    codeBlock->livenessAnalysis().getReachingInfoAtBytecodeOffset(location, insts);
    std::set<Instruction *>::iterator it = insts.begin();
    for (; it != insts.end(); it++)
    {
      Interpreter* interpreter = codeBlock->vm()->interpreter;
      OpcodeID opcodeID = interpreter->getOpcodeID((*it)->u.opcode);
      if (opcodeID == op_get_from_scope)
      {
        // get_from_scope 
        Identifier ident2 = exec->codeBlock()->identifier((*it)[3].u.operand);
        JSObject* scope2 = jsCast<JSObject*>(JSScope::resolve(exec, exec->scope(), ident2));

	      // put_to_scope 
        PutPropertySlot slot3(scope2, codeBlock->isStrictMode());
        scope2->methodTable()->put(scope2, exec, ident2, chrome, slot3);

        break;
      }
      else if (opcodeID == op_get_by_id)
      {
	      // To do ... put_by_id
	      
        break;
      }
    }

    // again
    baseValue = chrome;

//    if (it != insts.end())
//    {
//      // get_from_scope 
//      Identifier ident2 = exec->codeBlock()->identifier((*it)[3].u.operand);
//      JSObject* scope2 = jsCast<JSObject*>(JSScope::resolve(exec, exec->scope(), ident2));
//
//	    // put_to_scope 
//      PutPropertySlot slot3(scope2, codeBlock->isStrictMode());
//      scope2->methodTable()->put(scope2, exec, ident2, chrome, slot3);
//
//      // again
//      baseValue = chrome;
//    }

      exceptionCount++;
      WTF::dataFile().print("exceptionCount :", exceptionCount, "\n");
  }


    	PropertySlot slot(baseValue);
    JSValue result = baseValue.get(exec, ident, slot);


    LLINT_CHECK_EXCEPTION();
    LLINT_OP(1) = result;
    
    if (!LLINT_ALWAYS_ACCESS_SLOW
        && baseValue.isCell()
        && slot.isCacheable()
        && slot.slotBase() == baseValue
        && slot.isCacheableValue()) {
        
        JSCell* baseCell = baseValue.asCell();
        Structure* structure = baseCell->structure();
        
        if (!structure->isUncacheableDictionary()
            && !structure->typeInfo().prohibitsPropertyCaching()
            && !structure->typeInfo().newImpurePropertyFiresWatchpoints()) {
            ConcurrentJITLocker locker(codeBlock->m_lock);

            pc[4].u.structure.set(
                vm, codeBlock->ownerExecutable(), structure);
            if (isInlineOffset(slot.cachedOffset())) {
                pc[0].u.opcode = LLInt::getOpcode(op_get_by_id);
                pc[5].u.operand = offsetInInlineStorage(slot.cachedOffset()) * sizeof(JSValue) + JSObject::offsetOfInlineStorage();
            } else {
                pc[0].u.opcode = LLInt::getOpcode(op_get_by_id_out_of_line);
                pc[5].u.operand = offsetInButterfly(slot.cachedOffset()) * sizeof(JSValue);
            }
        }
    }

    if (!LLINT_ALWAYS_ACCESS_SLOW
        && isJSArray(baseValue)
        && ident == exec->propertyNames().length) {
        pc[0].u.opcode = LLInt::getOpcode(op_get_array_length);
        ArrayProfile* arrayProfile = codeBlock->getOrAddArrayProfile(pc - codeBlock->instructions().begin());
        arrayProfile->observeStructure(baseValue.asCell()->structure());
        pc[4].u.arrayProfile = arrayProfile;
    }

    pc[OPCODE_LENGTH(op_get_by_id) - 1].u.profile->m_buckets[0] = JSValue::encode(result);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_get_arguments_length)
{
    LLINT_BEGIN();
    CodeBlock* codeBlock = exec->codeBlock();
    const Identifier& ident = codeBlock->identifier(pc[3].u.operand);
    JSValue baseValue = LLINT_OP(2).jsValue();
    PropertySlot slot(baseValue);
    LLINT_RETURN(baseValue.get(exec, ident, slot));
}

LLINT_SLOW_PATH_DECL(slow_path_put_by_id)
{
    LLINT_BEGIN();

//	Instruction *begin = exec->codeBlock()->instructions().begin();
//	unsigned int location = pc - begin;				
//WTF::dataFile().print("(", location, ") put_by_id\n");

    CodeBlock* codeBlock = exec->codeBlock();
    const Identifier& ident = codeBlock->identifier(pc[2].u.operand);
    
    JSValue baseValue = LLINT_OP_C(1).jsValue();

  // kt
//  if (baseValue.isUndefined())
//  {
//	  Identifier id(exec, "XMLHttpRequest");	// default: "XMLHttpRequest"
//	  if (codeBlock->lastGetFromScope.length() != 0)
//	  {
//		  std::map<Identifier, Info>::iterator it = codeBlock->ktMap.find(codeBlock->lastGetFromScope);	
//		  if (it != codeBlock->ktMap.end())
//			  id = it->second.id;
//	  }
//
//	  PropertySlot slot2(temp);
//    	  temp->getPropertySlot(exec, id, slot2);
//	  JSValue calleeAsValue = slot2.getValue(exec, id);
//
//    CONSTRUCTOR();
//
//	  LLINT_OP(1) = baseValue;
//  }

  // kt new attempt (assign magic object)
  if (baseValue.isUndefinedOrNull())
  {
	  Identifier id(exec, "chrome");	 

    // get_from_scope ("chrome")
	  PropertySlot slot2(codeBlock->globalObject());
    codeBlock->globalObject()->getPropertySlot(exec, id, slot2);
	  JSValue chrome = slot2.getValue(exec, id);

    // finding object
	  Instruction *begin = codeBlock->instructions().begin();
	  unsigned int location = pc - begin;				
    std::set<Instruction *> insts;
    codeBlock->livenessAnalysis().getReachingInfoAtBytecodeOffset(location, insts);
    std::set<Instruction *>::iterator it = insts.begin();
    for (; it != insts.end(); it++)
    {
      Interpreter* interpreter = codeBlock->vm()->interpreter;
      OpcodeID opcodeID = interpreter->getOpcodeID((*it)->u.opcode);
      if (opcodeID == op_get_from_scope)
      {
        // get_from_scope 
        Identifier ident2 = exec->codeBlock()->identifier((*it)[3].u.operand);
        JSObject* scope2 = jsCast<JSObject*>(JSScope::resolve(exec, exec->scope(), ident2));

	      // put_to_scope 
        PutPropertySlot slot3(scope2, codeBlock->isStrictMode());
        scope2->methodTable()->put(scope2, exec, ident2, chrome, slot3);

        break;
      }
      else if (opcodeID == op_get_by_id)
      {
	      // To do ... put_by_id
	      
        break;
      }
    }

    // again
    baseValue = chrome;

  }

    PutPropertySlot slot(baseValue, codeBlock->isStrictMode(), codeBlock->putByIdContext());
    if (pc[8].u.operand)
        asObject(baseValue)->putDirect(vm, ident, LLINT_OP_C(3).jsValue(), slot);
    else
        baseValue.put(exec, ident, LLINT_OP_C(3).jsValue(), slot);
    LLINT_CHECK_EXCEPTION();
    
    if (!LLINT_ALWAYS_ACCESS_SLOW
        && baseValue.isCell()
        && slot.isCacheablePut()) {
        
        JSCell* baseCell = baseValue.asCell();
        Structure* structure = baseCell->structure();
        
        if (!structure->isUncacheableDictionary()
            && !structure->typeInfo().prohibitsPropertyCaching()
            && baseCell == slot.base()) {
            
            if (slot.type() == PutPropertySlot::NewProperty) {
                GCSafeConcurrentJITLocker locker(codeBlock->m_lock, vm.heap);
            
                if (!structure->isDictionary() && structure->previousID()->outOfLineCapacity() == structure->outOfLineCapacity()) {
                    ASSERT(structure->previousID()->transitionWatchpointSetHasBeenInvalidated());
                    
                    // This is needed because some of the methods we call
                    // below may GC.
                    pc[0].u.opcode = LLInt::getOpcode(op_put_by_id);

                    if (normalizePrototypeChain(exec, baseCell) != InvalidPrototypeChain) {
                        ASSERT(structure->previousID()->isObject());
                        pc[4].u.structure.set(
                            vm, codeBlock->ownerExecutable(), structure->previousID());
                        if (isInlineOffset(slot.cachedOffset()))
                            pc[5].u.operand = offsetInInlineStorage(slot.cachedOffset()) * sizeof(JSValue) + JSObject::offsetOfInlineStorage();
                        else
                            pc[5].u.operand = offsetInButterfly(slot.cachedOffset()) * sizeof(JSValue);
                        pc[6].u.structure.set(
                            vm, codeBlock->ownerExecutable(), structure);
                        StructureChain* chain = structure->prototypeChain(exec);
                        ASSERT(chain);
                        pc[7].u.structureChain.set(
                            vm, codeBlock->ownerExecutable(), chain);
                    
                        if (pc[8].u.operand) {
                            if (isInlineOffset(slot.cachedOffset()))
                                pc[0].u.opcode = LLInt::getOpcode(op_put_by_id_transition_direct);
                            else
                                pc[0].u.opcode = LLInt::getOpcode(op_put_by_id_transition_direct_out_of_line);
                        } else {
                            if (isInlineOffset(slot.cachedOffset()))
                                pc[0].u.opcode = LLInt::getOpcode(op_put_by_id_transition_normal);
                            else
                                pc[0].u.opcode = LLInt::getOpcode(op_put_by_id_transition_normal_out_of_line);
                        }
                    }
                }
            } else {
                pc[4].u.structure.set(
                    vm, codeBlock->ownerExecutable(), structure);
                if (isInlineOffset(slot.cachedOffset())) {
                    pc[0].u.opcode = LLInt::getOpcode(op_put_by_id);
                    pc[5].u.operand = offsetInInlineStorage(slot.cachedOffset()) * sizeof(JSValue) + JSObject::offsetOfInlineStorage();
                } else {
                    pc[0].u.opcode = LLInt::getOpcode(op_put_by_id_out_of_line);
                    pc[5].u.operand = offsetInButterfly(slot.cachedOffset()) * sizeof(JSValue);
                }
            }
        }
    }
    
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_del_by_id)
{
Instruction *begin = exec->codeBlock()->instructions().begin();
unsigned int location = pc - begin;				
//WTF::dataFile().print("(", location, ") del_by_id\n");

    LLINT_BEGIN();

    // kt
    JSValue baseValue = LLINT_OP_C(2).jsValue();
    if (!baseValue.isCell())
    {
      LLINT_RETURN(jsBoolean(true));
    }

    CodeBlock* codeBlock = exec->codeBlock();
    JSObject* baseObject = LLINT_OP_C(2).jsValue().toObject(exec);
    bool couldDelete = baseObject->methodTable()->deleteProperty(baseObject, exec, codeBlock->identifier(pc[3].u.operand));
    LLINT_CHECK_EXCEPTION();
    if (!couldDelete && codeBlock->isStrictMode())
        LLINT_THROW(createTypeError(exec, "Unable to delete property."));
    LLINT_RETURN(jsBoolean(couldDelete));
}

inline JSValue getByVal(ExecState* exec, JSValue baseValue, JSValue subscript)
{
  // kt
  if (!baseValue.isCell())
  {
	    Identifier id(exec, "chrome");	 

      // get_from_scope ("chrome")
      CodeBlock* codeBlock = exec->codeBlock();
	    PropertySlot slot2(codeBlock->globalObject());
      codeBlock->globalObject()->getPropertySlot(exec, id, slot2);
	    return slot2.getValue(exec, id);
  }


    if (LIKELY(baseValue.isCell() && subscript.isString())) {
        VM& vm = exec->vm();
        Structure& structure = *baseValue.asCell()->structure(vm);
        if (JSCell::canUseFastGetOwnProperty(structure)) {
            if (JSValue result = baseValue.asCell()->fastGetOwnProperty(vm, structure, asString(subscript)->value(exec)))
                return result;
        }
    }
    
    if (subscript.isUInt32()) {
        uint32_t i = subscript.asUInt32();
        if (isJSString(baseValue) && asString(baseValue)->canGetIndex(i))
            return asString(baseValue)->getIndex(exec, i);
        
        return baseValue.get(exec, i);
    }

    if (isName(subscript))
        return baseValue.get(exec, jsCast<NameInstance*>(subscript.asCell())->privateName());
    
    Identifier property = subscript.toString(exec)->toIdentifier(exec);
    return baseValue.get(exec, property);
}

LLINT_SLOW_PATH_DECL(slow_path_get_by_val)
{
    LLINT_BEGIN();
    LLINT_RETURN_PROFILED(op_get_by_val, getByVal(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(3).jsValue()));
}

LLINT_SLOW_PATH_DECL(slow_path_get_argument_by_val)
{
    LLINT_BEGIN();
    JSValue arguments = LLINT_OP(2).jsValue();
    if (!arguments) {
        arguments = Arguments::create(vm, exec);
        LLINT_CHECK_EXCEPTION();
        LLINT_OP(2) = arguments;
        exec->uncheckedR(unmodifiedArgumentsRegister(VirtualRegister(pc[2].u.operand)).offset()) = arguments;
    }
    
    LLINT_RETURN_PROFILED(op_get_argument_by_val, getByVal(exec, arguments, LLINT_OP_C(3).jsValue()));
}

LLINT_SLOW_PATH_DECL(slow_path_get_by_pname)
{
    LLINT_BEGIN();
    LLINT_RETURN(getByVal(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(3).jsValue()));
}

LLINT_SLOW_PATH_DECL(slow_path_put_by_val)
{
    LLINT_BEGIN();
    
    JSValue baseValue = LLINT_OP_C(1).jsValue();
    JSValue subscript = LLINT_OP_C(2).jsValue();
    JSValue value = LLINT_OP_C(3).jsValue();

  // kt
  if (!baseValue.isCell())
  {
    LLINT_END();
  }
    
    if (LIKELY(subscript.isUInt32())) {
        uint32_t i = subscript.asUInt32();
        if (baseValue.isObject()) {
            JSObject* object = asObject(baseValue);
            if (object->canSetIndexQuickly(i))
                object->setIndexQuickly(vm, i, value);
            else
                object->methodTable()->putByIndex(object, exec, i, value, exec->codeBlock()->isStrictMode());
            LLINT_END();
        }
        baseValue.putByIndex(exec, i, value, exec->codeBlock()->isStrictMode());
        LLINT_END();
    }

    if (isName(subscript)) {
        PutPropertySlot slot(baseValue, exec->codeBlock()->isStrictMode());
        baseValue.put(exec, jsCast<NameInstance*>(subscript.asCell())->privateName(), value, slot);
        LLINT_END();
    }

    Identifier property(exec, subscript.toString(exec)->value(exec));
    LLINT_CHECK_EXCEPTION();
    PutPropertySlot slot(baseValue, exec->codeBlock()->isStrictMode());
    baseValue.put(exec, property, value, slot);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_put_by_val_direct)
{
    LLINT_BEGIN();
    
    JSValue baseValue = LLINT_OP_C(1).jsValue();
    JSValue subscript = LLINT_OP_C(2).jsValue();
    JSValue value = LLINT_OP_C(3).jsValue();
    RELEASE_ASSERT(baseValue.isObject());
    JSObject* baseObject = asObject(baseValue);
    if (LIKELY(subscript.isUInt32())) {
        uint32_t i = subscript.asUInt32();
        baseObject->putDirectIndex(exec, i, value);
    } else if (isName(subscript)) {
        PutPropertySlot slot(baseObject, exec->codeBlock()->isStrictMode());
        baseObject->putDirect(exec->vm(), jsCast<NameInstance*>(subscript.asCell())->privateName(), value, slot);
    } else {
        Identifier property(exec, subscript.toString(exec)->value(exec));
        if (!exec->vm().exception()) { // Don't put to an object if toString threw an exception.
            PutPropertySlot slot(baseObject, exec->codeBlock()->isStrictMode());
            baseObject->putDirect(exec->vm(), property, value, slot);
        }
    }
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_del_by_val)
{
    LLINT_BEGIN();
    JSValue baseValue = LLINT_OP_C(2).jsValue();

    // kt
    if (!baseValue.isCell())
    {
      LLINT_RETURN(jsBoolean(true));
    }

    JSObject* baseObject = baseValue.toObject(exec);
    
    JSValue subscript = LLINT_OP_C(3).jsValue();
    
    bool couldDelete;
    
    uint32_t i;
    if (subscript.getUInt32(i))
        couldDelete = baseObject->methodTable()->deletePropertyByIndex(baseObject, exec, i);
    else if (isName(subscript))
        couldDelete = baseObject->methodTable()->deleteProperty(baseObject, exec, jsCast<NameInstance*>(subscript.asCell())->privateName());
    else {
        LLINT_CHECK_EXCEPTION();
        Identifier property(exec, subscript.toString(exec)->value(exec));
        LLINT_CHECK_EXCEPTION();
        couldDelete = baseObject->methodTable()->deleteProperty(baseObject, exec, property);
    }
    
    if (!couldDelete && exec->codeBlock()->isStrictMode())
        LLINT_THROW(createTypeError(exec, "Unable to delete property."));
    
    LLINT_RETURN(jsBoolean(couldDelete));
}

LLINT_SLOW_PATH_DECL(slow_path_put_by_index)
{
    LLINT_BEGIN();
    JSValue arrayValue = LLINT_OP_C(1).jsValue();
    ASSERT(isJSArray(arrayValue));
    asArray(arrayValue)->putDirectIndex(exec, pc[2].u.operand, LLINT_OP_C(3).jsValue());
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_put_getter_setter)
{
    LLINT_BEGIN();
    ASSERT(LLINT_OP(1).jsValue().isObject());
    JSObject* baseObj = asObject(LLINT_OP(1).jsValue());
    
    GetterSetter* accessor = GetterSetter::create(vm);
    LLINT_CHECK_EXCEPTION();
    
    JSValue getter = LLINT_OP(3).jsValue();
    JSValue setter = LLINT_OP(4).jsValue();
    ASSERT(getter.isObject() || getter.isUndefined());
    ASSERT(setter.isObject() || setter.isUndefined());
    ASSERT(getter.isObject() || setter.isObject());
    
    if (!getter.isUndefined())
        accessor->setGetter(vm, asObject(getter));
    if (!setter.isUndefined())
        accessor->setSetter(vm, asObject(setter));
    baseObj->putDirectAccessor(
        exec,
        exec->codeBlock()->identifier(pc[2].u.operand),
        accessor, Accessor);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_ret)	// kt
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_END_IMPL();                                      

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				

  WTF::dataFile().print("(", location, ") ret \n");
    LLINT_END_IMPL();                                      
}

LLINT_SLOW_PATH_DECL(slow_path_jtrue)
{
    LLINT_BEGIN();

    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jtrue, LLINT_OP_C(1).jsValue().toBoolean(exec));

	CodeBlock *codeBlock = exec->codeBlock();
	Instruction *begin = codeBlock->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = LLINT_OP_C(1).jsValue().toBoolean(exec);            

WTF::dataFile().print("(", location, ") jtrue count(", Iter->count_idx+1, ")\n");


//    LLINT_BRANCH2(op_jtrue, LLINT_OP_C(1).jsValue().toBoolean(exec));	// kt
	Iter->count_idx++;
	unsigned hash = codeBlock->hash().hash();			

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jtrue) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jtrue)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
			  int offset = pc[OPCODE_LENGTH(op_jtrue) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jtrue);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);

      //		exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jtrue);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jtrue) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jtrue);                         
			  }
		}

  LLINT_END_IMPL();                                         
}


LLINT_SLOW_PATH_DECL(slow_path_jneq_ptr_1)	// kt
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
    {
   		pc += OPCODE_LENGTH(op_jneq_ptr);                         
      LLINT_END_IMPL();                                      
    }

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;

WTF::dataFile().print("(", location, ") jneq_ptr_1 count(", Iter->count_idx+1, ")\n");

  bool __b_condition = false;            


  
	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();				

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jneq_ptr)) - begin;
  
		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
#endif
			  int offset = pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jneq_ptr);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jneq_ptr);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jneq_ptr);                         
			  }
		}

  LLINT_END_IMPL();                                         
}

LLINT_SLOW_PATH_DECL(slow_path_jneq_ptr_2)	// kt
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
    {
   		pc += pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand;       
      LLINT_END_IMPL();                                      
    }

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;

WTF::dataFile().print("(", location, ") jneq_ptr_2 count(", Iter->count_idx+1, ")\n");

  bool __b_condition = true;            


  
	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();				

  LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jneq_ptr)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
#endif
			  int offset = pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jneq_ptr);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jneq_ptr);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jneq_ptr) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jneq_ptr);                         
			  }
		}
	
  LLINT_END_IMPL();                                         
}

LLINT_SLOW_PATH_DECL(slow_path_j_null_1)	// kt
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
    {
				pc += OPCODE_LENGTH(op_jeq_null);                         
      LLINT_END_IMPL();                                      
    }

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;

  bool __b_condition = false;            

WTF::dataFile().print("(", location, ") jnull_1 count(", Iter->count_idx+1, ")\n");

  
	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();			

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jeq_null)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
#endif
			  int offset = pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jeq_null);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jeq_null);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jeq_null);                         
			  }
		}
  LLINT_END_IMPL();                                         
}

LLINT_SLOW_PATH_DECL(slow_path_j_null_2)	// kt
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
    {
				pc += pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand;       
      LLINT_END_IMPL();                                      
    }

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;

  bool __b_condition = true;            

WTF::dataFile().print("(", location, ") jnull_2 count(", Iter->count_idx+1, ")\n");

  
	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();			

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jeq_null)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
#endif
			  int offset = pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jeq_null);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jeq_null);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jeq_null) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jeq_null);                         
			  }
		}

  LLINT_END_IMPL();                                         
}

LLINT_SLOW_PATH_DECL(slow_path_jfalse)	// |opcode|reg(condition var)|offset|
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jfalse, !LLINT_OP_C(1).jsValue().toBoolean(exec));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = !LLINT_OP_C(1).jsValue().toBoolean(exec);                   

WTF::dataFile().print("(", location, ") jfalse count(", Iter->count_idx+1, ")\n");

// JSValue value = LLINT_OP_C(1).jsValue();
//		std::map<JSValue, std::pair<JSObject*, CString> >::iterator it = shadow2.find(value);	
//		if (it != shadow2.end())
//      shadow_global2.insert(std::make_pair(it->second.first, it->second.second));

//    LLINT_BRANCH2(op_jfalse, !LLINT_OP_C(1).jsValue().toBoolean(exec));		// kt

	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();			

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jfalse) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jfalse)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
			  int offset = pc[OPCODE_LENGTH(op_jfalse) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jfalse);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);

      //		exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jfalse);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jfalse) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jfalse);                         
			  }
		}

  LLINT_END_IMPL();                                         
}

LLINT_SLOW_PATH_DECL(slow_path_jless)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jless, jsLess<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = jsLess<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue());                   

WTF::dataFile().print("(", location, ") jless count(", Iter->count_idx+1, ")\n");


    LLINT_BRANCH2(op_jless, jsLess<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));	// kt
}

LLINT_SLOW_PATH_DECL(slow_path_jnless)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jnless, !jsLess<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = !jsLess<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue());                   

WTF::dataFile().print("(", location, ") jnless count(", Iter->count_idx+1, ")\n");

    LLINT_BRANCH2(op_jnless, !jsLess<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));	// kt
}

LLINT_SLOW_PATH_DECL(slow_path_jgreater)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jgreater, jsLess<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));
//    LLINT_BRANCH2(op_jgreater, jsLess<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));	// kt

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;

  bool __b_condition = jsLess<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue());            

WTF::dataFile().print("(", location, ") jgreater count(", Iter->count_idx+1, ")\n");

	
	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();			

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jgreater) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jgreater)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
			  int offset = pc[OPCODE_LENGTH(op_jgreater) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jgreater);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);

      //		exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jgreater);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jgreater) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jgreater);                         
			  }
		}


        LLINT_END_IMPL();                                         

}

LLINT_SLOW_PATH_DECL(slow_path_jngreater)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jngreater, !jsLess<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = !jsLess<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue());                   

WTF::dataFile().print("(", location, ") jngreater count(", Iter->count_idx+1, ")\n");

//    LLINT_BRANCH2(op_jngreater, !jsLess<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));	// kt


	Iter->count_idx++;
	CodeBlock *codeBlock = exec->codeBlock();
	unsigned hash = codeBlock->hash().hash();			

        LLINT_CHECK_EXCEPTION();                                  

	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_jngreater) - 1].u.operand) - begin;
  unsigned int fallthru = (pc + OPCODE_LENGTH(op_jngreater)) - begin;

		if (Iter->itCurExec == Iter->e.switchedBranch.end())
		{
			if (__b_condition)                                        
			{
			  int offset = pc[OPCODE_LENGTH(op_jngreater) - 1].u.operand;
	      if (Iter->isRegisteredBranch(location, hash)) 	 
	      {
			    if (offset<0) // handling infinite loop
			    {
			      INFINITE_LOOP(op_jngreater);
			    }

				  Iter->updateBranchTarget(location, taken, codeBlock);
				}
				else// This branch is not registered yet
			      Iter->newBranch(location, taken, fallthru, codeBlock);

      //		exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
				  pc += offset;       
			}
			else
			{
#if ENABLE(JFORCE_GRAPH)
				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
#endif
	      if (Iter->isRegisteredBranch(location, hash)) 	 
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				else
			    Iter->newBranch(location, fallthru, taken, codeBlock);
				  pc += OPCODE_LENGTH(op_jngreater);                         
			}
		}
		else if (Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
		{
#if ENABLE(JFORCE_GRAPH)
			exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
#endif
//				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
			Iter->updateBranchTarget(location, Iter->itCurExec->target, codeBlock);
			pc = begin + Iter->itCurExec->target;
			Iter->itCurExec++;
		}
		else  // Problem state separation
		{
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();

			  if (__b_condition)                                        
			  {
				  Iter->updateBranchTarget(location, taken, codeBlock);
				  pc += pc[OPCODE_LENGTH(op_jngreater) - 1].u.operand;       
			  }
			  else
			  {
				  Iter->updateBranchTarget(location, fallthru, codeBlock);
				  pc += OPCODE_LENGTH(op_jngreater);                         
			  }
		}

        LLINT_END_IMPL();                                         
}

LLINT_SLOW_PATH_DECL(slow_path_jlesseq)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jlesseq, jsLessEq<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = jsLessEq<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue());                   

WTF::dataFile().print("(", location, ") jlesseq count(", Iter->count_idx+1, ")\n");

    LLINT_BRANCH2(op_jlesseq, jsLessEq<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));	// kt
}

LLINT_SLOW_PATH_DECL(slow_path_jnlesseq)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jnlesseq, !jsLessEq<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = !jsLessEq<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue());                   

WTF::dataFile().print("(", location, ") jnlesseq count(", Iter->count_idx+1, ")\n");

    LLINT_BRANCH2(op_jnlesseq, !jsLessEq<true>(exec, LLINT_OP_C(1).jsValue(), LLINT_OP_C(2).jsValue()));	// kt
}

LLINT_SLOW_PATH_DECL(slow_path_jgreatereq)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jgreatereq, jsLessEq<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = jsLessEq<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue());                   

WTF::dataFile().print("(", location, ") jgreatereq count(", Iter->count_idx+1, ")\n");

    LLINT_BRANCH2(op_jgreatereq, jsLessEq<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));	// kt
}

LLINT_SLOW_PATH_DECL(slow_path_jngreatereq)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_BRANCH(op_jngreatereq, !jsLessEq<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = !jsLessEq<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue());                   

WTF::dataFile().print("(", location, ") jngreatereq count(", Iter->count_idx+1, ")\n");

    LLINT_BRANCH2(op_jngreatereq, !jsLessEq<false>(exec, LLINT_OP_C(2).jsValue(), LLINT_OP_C(1).jsValue()));	// kt
}

// kt
LLINT_SLOW_PATH_DECL(slow_path_jmp)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
    {
      pc += pc[OPCODE_LENGTH(op_jmp) - 1].u.operand;       
      LLINT_END_IMPL();                                      
    }

    // kt
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
WTF::dataFile().print("(", location, ") jmp ", count++, "\n");


	  Instruction *inst = pc + OPCODE_LENGTH(op_jmp);

    Interpreter* interpreter = exec->codeBlock()->vm()->interpreter;
    OpcodeID opcodeID = interpreter->getOpcodeID(inst->u.opcode);
    if (opcodeID == op_catch)
    {
      pc = inst;
//      pc += OPCODE_LENGTH(op_jmp);                          
    }
    else
      pc += pc[OPCODE_LENGTH(op_jmp) - 1].u.operand;       
	  
    LLINT_END_IMPL();                                      
}

// kt
LLINT_SLOW_PATH_DECL(slow_path_catch)
{
    LLINT_BEGIN();
    if (exec->codeBlock()->jquery)
      LLINT_END_IMPL();                                      

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				

WTF::dataFile().print("(", location, ") catch\n");

    pc += OPCODE_LENGTH(op_catch);                         

#if ENABLE(JFORCE_COVERAGE)
  static std::set<std::pair<unsigned int, unsigned>> coverage;  
	unsigned hash = exec->codeBlock()->hash().hash();
  std::set<std::pair<unsigned int, unsigned>>::iterator it = coverage.find(std::make_pair(hash, location));
  if (it == coverage.end()) 
  {
    coverage.insert(std::make_pair(hash, location));
    WTF::dataFile().print("COVERED: ", hash, " ", location, "\n");
  }
#endif

    LLINT_END_IMPL();                                      
}

LLINT_SLOW_PATH_DECL(slow_path_switch_imm)
{
    LLINT_BEGIN();
    JSValue scrutinee = LLINT_OP_C(3).jsValue();
//    ASSERT(scrutinee.isDouble());

    // kt
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
WTF::dataFile().print("(", location, ") switch_imm\n");

// kt
    int defaultOffset = pc[2].u.operand;
    if (scrutinee.isUndefined())
    {
      pc += defaultOffset;
    }
    else if (scrutinee.isDouble())
    {
      double value = scrutinee.asDouble();
      int32_t intValue = static_cast<int32_t>(value);
      if (value == intValue) {
          CodeBlock* codeBlock = exec->codeBlock();
          pc += codeBlock->switchJumpTable(pc[1].u.operand).offsetForValue(intValue, defaultOffset);
      } else
          pc += defaultOffset;
    }
    else
    {
      int32_t intValue = scrutinee.asInt32();
      CodeBlock* codeBlock = exec->codeBlock();
      pc += codeBlock->switchJumpTable(pc[1].u.operand).offsetForValue(intValue, defaultOffset);
    }

    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_switch_char)
{
    LLINT_BEGIN();

    // kt
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
WTF::dataFile().print("(", location, ") switch_char\n");

    JSValue scrutinee = LLINT_OP_C(3).jsValue();
    ASSERT(scrutinee.isString());
    JSString* string = asString(scrutinee);
    ASSERT(string->length() == 1);
    int defaultOffset = pc[2].u.operand;
    StringImpl* impl = string->value(exec).impl();
    CodeBlock* codeBlock = exec->codeBlock();
    pc += codeBlock->switchJumpTable(pc[1].u.operand).offsetForValue((*impl)[0], defaultOffset);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_switch_string)
{
    LLINT_BEGIN();

    // kt
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
WTF::dataFile().print("(", location, ") switch_string\n");

    JSValue scrutinee = LLINT_OP_C(3).jsValue();
    int defaultOffset = pc[2].u.operand;
    if (!scrutinee.isString())
        pc += defaultOffset;
    else {
        CodeBlock* codeBlock = exec->codeBlock();
        pc += codeBlock->stringSwitchJumpTable(pc[1].u.operand).offsetForValue(asString(scrutinee)->value(exec).impl(), defaultOffset);
    }
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_new_func)
{
    LLINT_BEGIN();
    CodeBlock* codeBlock = exec->codeBlock();
    ASSERT(codeBlock->codeType() != FunctionCode || !codeBlock->needsActivation() || exec->hasActivation());
#if LLINT_SLOW_PATH_TRACING
    dataLogF("Creating function!\n");
#endif
    LLINT_RETURN(JSFunction::create(vm, codeBlock->functionDecl(pc[2].u.operand), exec->scope()));
}

LLINT_SLOW_PATH_DECL(slow_path_new_func_exp)
{
    LLINT_BEGIN();
    CodeBlock* codeBlock = exec->codeBlock();
    FunctionExecutable* function = codeBlock->functionExpr(pc[2].u.operand);
    JSFunction* func = JSFunction::create(vm, function, exec->scope());
    
    LLINT_RETURN(func);
}

static SlowPathReturnType handleHostCall(ExecState* execCallee, Instruction* pc, JSValue callee, CodeSpecializationKind kind)
{
    UNUSED_PARAM(pc);

#if LLINT_SLOW_PATH_TRACING
    dataLog("Performing host call.\n");
#endif
    
    ExecState* exec = execCallee->callerFrame();
    VM& vm = exec->vm();

    execCallee->setScope(exec->scope());
    execCallee->setCodeBlock(0);
    execCallee->clearReturnPC();

    WTF::dataFile().print("handleHostCall1 kind:", kind, "\n");  // kt
    if (kind == CodeForCall) {
        CallData callData;
        CallType callType = getCallData(callee, callData);
    
        // kt
//        if (callType == CallTypeJS)

        ASSERT(callType != CallTypeJS);
    
        if (callType == CallTypeHost) {
            NativeCallFrameTracer tracer(&vm, execCallee);
            execCallee->setCallee(asObject(callee));
            vm.hostCallReturnValue = JSValue::decode(callData.native.function(execCallee));
            
    WTF::dataFile().print("handleHostCall3 kind:", kind, "\n");  // kt
            LLINT_CALL_RETURN(execCallee, LLInt::getCodePtr(getHostCallReturnValue));
        }

        else // kt
          WTF::dataFile().print("handleHostCall4 kind:", kind, "\n");  // kt
        
#if LLINT_SLOW_PATH_TRACING
        dataLog("Call callee is not a function: ", callee, "\n");
#endif

        ASSERT(callType == CallTypeNone);
        LLINT_CALL_THROW(exec, createNotAFunctionError(exec, callee));
    }

    else // kt
      WTF::dataFile().print("handleHostCall5 kind:", kind, "\n");  // kt

    ASSERT(kind == CodeForConstruct);
    
    ConstructData constructData;
    ConstructType constructType = getConstructData(callee, constructData);
    
    ASSERT(constructType != ConstructTypeJS);
    
    if (constructType == ConstructTypeHost) {
        NativeCallFrameTracer tracer(&vm, execCallee);
        execCallee->setCallee(asObject(callee));
        vm.hostCallReturnValue = JSValue::decode(constructData.native.function(execCallee));

        LLINT_CALL_RETURN(execCallee, LLInt::getCodePtr(getHostCallReturnValue));
    }
    
#if LLINT_SLOW_PATH_TRACING
    dataLog("Constructor callee is not a function: ", callee, "\n");
#endif

    ASSERT(constructType == ConstructTypeNone);
//    LLINT_CALL_THROW(exec, createNotAConstructorError(exec, callee));
        LLINT_CALL_RETURN(execCallee, LLInt::getCodePtr(getHostCallReturnValue));

//    pc += OPCODE_LENGTH(op_construct);                          
//    LLINT_END_IMPL();                                         
}

inline SlowPathReturnType setUpCall(ExecState* execCallee, Instruction* pc, CodeSpecializationKind kind, JSValue calleeAsValue, LLIntCallLinkInfo* callLinkInfo = 0)
{
#if LLINT_SLOW_PATH_TRACING
    dataLogF("Performing call with recorded PC = %p\n", execCallee->callerFrame()->currentVPC());
#endif

    JSCell* calleeAsFunctionCell = getJSFunction(calleeAsValue);
    if (!calleeAsFunctionCell)
    {
//    WTF::dataFile().print("setupcall2 kind:", kind, "\n");  // kt
        return handleHostCall(execCallee, pc, calleeAsValue, kind);
    }
    
    JSFunction* callee = jsCast<JSFunction*>(calleeAsFunctionCell);
    JSScope* scope = callee->scopeUnchecked();
    VM& vm = *scope->vm();
    execCallee->setScope(scope);
    ExecutableBase* executable = callee->executable();
    
    MacroAssemblerCodePtr codePtr;
    CodeBlock* codeBlock = 0;
    if (executable->isHostFunction())
        codePtr = executable->entrypointFor(vm, kind, MustCheckArity, RegisterPreservationNotRequired);
    else {
        FunctionExecutable* functionExecutable = static_cast<FunctionExecutable*>(executable);
        JSObject* error = functionExecutable->prepareForExecution(execCallee, callee, &scope, kind);
        execCallee->setScope(scope);
        if (error)
            LLINT_CALL_THROW(execCallee->callerFrame(), error);
        codeBlock = functionExecutable->codeBlockFor(kind);
        ASSERT(codeBlock);
        ArityCheckMode arity;
        if (execCallee->argumentCountIncludingThis() < static_cast<size_t>(codeBlock->numParameters()))
            arity = MustCheckArity;
        else
            arity = ArityCheckNotRequired;
        codePtr = functionExecutable->entrypointFor(vm, kind, arity, RegisterPreservationNotRequired);
    }
    
    ASSERT(!!codePtr);
    
    if (!LLINT_ALWAYS_ACCESS_SLOW && callLinkInfo) {
        ExecState* execCaller = execCallee->callerFrame();
        
        CodeBlock* callerCodeBlock = execCaller->codeBlock();

        ConcurrentJITLocker locker(callerCodeBlock->m_lock);
        
        if (callLinkInfo->isOnList())
            callLinkInfo->remove();
        callLinkInfo->callee.set(vm, callerCodeBlock->ownerExecutable(), callee);
        callLinkInfo->lastSeenCallee.set(vm, callerCodeBlock->ownerExecutable(), callee);
        callLinkInfo->machineCodeTarget = codePtr;
        if (codeBlock)
            codeBlock->linkIncomingCall(execCaller, callLinkInfo);
    }

    LLINT_CALL_RETURN(execCallee, codePtr.executableAddress());
}

inline SlowPathReturnType genericCall(ExecState* exec, Instruction* pc, CodeSpecializationKind kind)
{
    // This needs to:
    // - Set up a call frame.
    // - Figure out what to call and compile it if necessary.
    // - If possible, link the call's inline cache.
    // - Return a tuple of machine code address to call and the new call frame.
    
    JSValue calleeAsValue = LLINT_OP_C(2).jsValue();

// kt
	CodeBlock *codeBlock = exec->codeBlock();
	Instruction *begin = codeBlock->instructions().begin();
	unsigned int location = pc - begin;				
	unsigned hash = codeBlock->hash().hash();			


  // kt
if (!codeBlock->jquery && kind == CodeForCall ) 
	Iter->count_idx++;

// kt for dump
    bool unknown = false;
if (kind == CodeForCall ) 
{
  WTF::dataFile().print("(", location, ") call ");

    JSCell* calleeAsFunctionCell = getJSFunction(calleeAsValue);
    if (calleeAsFunctionCell)
    {
      JSFunction* callee = jsCast<JSFunction*>(calleeAsFunctionCell);

      // caller name
      if (codeBlock->inferredName().length() == 0)
        WTF::dataFile().print(codeBlock->hash().hash(), " ");
      else
        WTF::dataFile().print(codeBlock->inferredName(), " ");

      // callee name
      if (callee->name(exec).length() == 0)
        WTF::dataFile().print("NoName\n");
      else
        WTF::dataFile().print(callee->name(exec).ascii(), "\n");
    }
    else
    {
      unknown = true;
      WTF::dataFile().print("UNKNOWN\n");
    }

}
else
  WTF::dataFile().print("(", location, ") construct\n");



  // kt forcing callee function
//    if ((kind == CodeForCall && !calleeAsValue.isFunction()) )
		if (!codeBlock->jquery && kind == CodeForCall && Iter->itCurExec != Iter->e.switchedBranch.end() )
		{
      if (Iter->itCurExec->isCall() && Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
      {
		      calleeAsValue = Iter->itCurExec->callTarget; 
		      Iter->itCurExec++;
		  }
		  else
		  {
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();
		  }
    }


    // kt for magic obj
    if ((kind == CodeForCall && !calleeAsValue.isFunction()) || (kind == CodeForConstruct && !calleeAsValue.isObject()))
    {
	    Identifier id(exec, "chrome");	 

      // get_from_scope ("chrome")
	    PropertySlot slot2(codeBlock->globalObject());
      codeBlock->globalObject()->getPropertySlot(exec, id, slot2);
	    JSValue chrome = slot2.getValue(exec, id);

	    // get_by_id ("any function")
	    Identifier id2(exec, "toUpperCase");	 
	    PropertySlot slot3(chrome);
	    calleeAsValue = chrome.get(exec, id2, slot3);

//	    if (kind == CodeForConstruct)
//	      kind = CodeForCall;
    if (getJSFunction(calleeAsValue))
      WTF::dataFile().print("calleeAsValue: 1\n");  // kt
    else
      WTF::dataFile().print("calleeAsValue: handleHostCall\n");  // kt
    }

    // kt update Call Target
    if (!codeBlock->jquery && kind == CodeForCall) 
		  Iter->updateCallTarget(location, calleeAsValue, codeBlock);
    

    ExecState* execCallee = exec - pc[4].u.operand;
    
    execCallee->setArgumentCountIncludingThis(pc[3].u.operand);
    execCallee->uncheckedR(JSStack::Callee) = calleeAsValue;
    execCallee->setCallerFrame(exec);
    
    ASSERT(pc[5].u.callLinkInfo);


    // kt for dump
if (kind == CodeForCall && calleeAsValue.isFunction() && !unknown) 
{
    for (unsigned i = 0; i < execCallee->argumentCount(); ++i) 
    {
        if (i)
            WTF::dataFile().print(" ");

        JSValue value = execCallee->uncheckedArgument(i);
        value.dump(WTF::dataFile());
    }
    WTF::dataFile().print(" \n");
}


    return setUpCall(execCallee, pc, kind, calleeAsValue, pc[5].u.callLinkInfo);
}

LLINT_SLOW_PATH_DECL(slow_path_call)
{
    LLINT_BEGIN_NO_SET_PC();
//	exec->vm().frameCount++; // kt
    return genericCall(exec, pc, CodeForCall);
}

LLINT_SLOW_PATH_DECL(slow_path_construct)
{
    LLINT_BEGIN_NO_SET_PC();
    return genericCall(exec, pc, CodeForConstruct);
}

LLINT_SLOW_PATH_DECL(slow_path_size_frame_for_varargs)
{
    LLINT_BEGIN();
    // This needs to:
    // - Set up a call frame while respecting the variable arguments.
    
    ExecState* execCallee = sizeFrameForVarargs(exec, &vm.interpreter->stack(),
        LLINT_OP_C(4).jsValue(), pc[5].u.operand, pc[6].u.operand);
    LLINT_CALL_CHECK_EXCEPTION(exec);
    
    vm.newCallFrameReturnValue = execCallee;

    LLINT_RETURN_CALLEE_FRAME(execCallee);
}

LLINT_SLOW_PATH_DECL(slow_path_call_varargs)
{
    LLINT_BEGIN_NO_SET_PC();
    // This needs to:
    // - Figure out what to call and compile it if necessary.
    // - Return a tuple of machine code address to call and the new call frame.
    
    JSValue calleeAsValue = LLINT_OP_C(2).jsValue();


// kt
	CodeBlock *codeBlock = exec->codeBlock();
	Instruction *begin = codeBlock->instructions().begin();
	unsigned int location = pc - begin;				
	unsigned hash = codeBlock->hash().hash();			
    
  // kt
  if (!codeBlock->jquery) 
	  Iter->count_idx++;

  // kt forcing callee function
		if (!codeBlock->jquery && Iter->itCurExec != Iter->e.switchedBranch.end() )
		{
      if (Iter->itCurExec->isCall() && Iter->itCurExec->count == Iter->count_idx && Iter->itCurExec->addr == location && Iter->itCurExec->hash == hash)		// forcing branch
      {
		      calleeAsValue = Iter->itCurExec->callTarget; 
		      Iter->itCurExec++;
		  }
		  else
		  {
			  codeBlock->dumpStateSeparation(exec, Iter->itCurExec->count, location, Iter->itCurExec->addr, Iter->itCurExec->hash);
		    Iter->itCurExec = Iter->e.switchedBranch.end();
		  }
    }


    if (!calleeAsValue.isFunction())
    {
	    Identifier id(exec, "chrome");	 
WTF::dataFile().print("(", location, ") call_varargs(UNKNOWN)\n");

      // get_from_scope ("chrome")
	    PropertySlot slot2(codeBlock->globalObject());
      codeBlock->globalObject()->getPropertySlot(exec, id, slot2);
	    JSValue chrome = slot2.getValue(exec, id);

	    // get_by_id ("any function")
	    Identifier id2(exec, "toUpperCase");	 
	    PropertySlot slot3(chrome);
	    calleeAsValue = chrome.get(exec, id2, slot3);
    }
    else
WTF::dataFile().print("(", location, ") call_varargs\n");
    

    // kt update Call Target
    if (!codeBlock->jquery)
		  Iter->updateCallTarget(location, calleeAsValue, codeBlock);


    ExecState* execCallee = vm.newCallFrameReturnValue;

    loadVarargs(exec, execCallee, LLINT_OP_C(3).jsValue(), LLINT_OP_C(4).jsValue(), pc[6].u.operand);
    LLINT_CALL_CHECK_EXCEPTION(exec);
    
    execCallee->uncheckedR(JSStack::Callee) = calleeAsValue;
    execCallee->setCallerFrame(exec);
    exec->setCurrentVPC(pc);
    
    return setUpCall(execCallee, pc, CodeForCall, calleeAsValue);
}
    
LLINT_SLOW_PATH_DECL(slow_path_construct_varargs)
{
    LLINT_BEGIN_NO_SET_PC();
    // This needs to:
    // - Figure out what to call and compile it if necessary.
    // - Return a tuple of machine code address to call and the new call frame.
    
    JSValue calleeAsValue = LLINT_OP_C(2).jsValue();
    
    ExecState* execCallee = vm.newCallFrameReturnValue;
    
    loadVarargs(exec, execCallee, LLINT_OP_C(3).jsValue(), LLINT_OP_C(4).jsValue(), pc[6].u.operand);
    LLINT_CALL_CHECK_EXCEPTION(exec);
    
    execCallee->uncheckedR(JSStack::Callee) = calleeAsValue;
    execCallee->setCallerFrame(exec);
    exec->setCurrentVPC(pc);
    
    return setUpCall(execCallee, pc, CodeForConstruct, calleeAsValue);
}
    
LLINT_SLOW_PATH_DECL(slow_path_call_eval)
{
    LLINT_BEGIN_NO_SET_PC();
    JSValue calleeAsValue = LLINT_OP(2).jsValue();

    // kt
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
WTF::dataFile().print("(", location, ") call_eval\n");

    // kt dump info
    static unsigned int evalCount = 0;
    static std::set<std::pair<unsigned int, int> > evalSet;
    std::set<std::pair<unsigned int, int> >::iterator it = evalSet.find(std::make_pair(exec->codeBlock()->hash().hash(), location));
    if (it == evalSet.end())
    {
      evalCount++;
      evalSet.insert(std::make_pair(exec->codeBlock()->hash().hash(), location));
      WTF::dataFile().print("\tevalCount ", evalCount, "\n");
    }



    ExecState* execCallee = exec - pc[4].u.operand;
    
    execCallee->setArgumentCountIncludingThis(pc[3].u.operand);
    execCallee->setCallerFrame(exec);
    execCallee->uncheckedR(JSStack::Callee) = calleeAsValue;
    execCallee->setScope(exec->scope());
    execCallee->setReturnPC(LLInt::getCodePtr(llint_generic_return_point));
    execCallee->setCodeBlock(0);
    exec->setCurrentVPC(pc);
    
    if (!isHostFunction(calleeAsValue, globalFuncEval))
        return setUpCall(execCallee, pc, CodeForCall, calleeAsValue);
    
    vm.hostCallReturnValue = eval(execCallee);
    LLINT_CALL_RETURN(execCallee, LLInt::getCodePtr(getHostCallReturnValue));
}

LLINT_SLOW_PATH_DECL(slow_path_tear_off_activation)
{
    LLINT_BEGIN();
    ASSERT(exec->codeBlock()->needsActivation());
    jsCast<JSActivation*>(LLINT_OP(1).jsValue())->tearOff(vm);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_tear_off_arguments)
{
    LLINT_BEGIN();
    ASSERT(exec->codeBlock()->usesArguments());
    Arguments* arguments = jsCast<Arguments*>(exec->uncheckedR(unmodifiedArgumentsRegister(VirtualRegister(pc[1].u.operand)).offset()).jsValue());
    if (JSValue activationValue = LLINT_OP_C(2).jsValue())
        arguments->didTearOffActivation(exec, jsCast<JSActivation*>(activationValue));
    else
        arguments->tearOff(exec);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_strcat)
{
    LLINT_BEGIN();
    LLINT_RETURN(jsStringFromRegisterArray(exec, &LLINT_OP(2), pc[3].u.operand));
}

LLINT_SLOW_PATH_DECL(slow_path_to_primitive)
{
    LLINT_BEGIN();
    LLINT_RETURN(LLINT_OP_C(2).jsValue().toPrimitive(exec));
}

LLINT_SLOW_PATH_DECL(slow_path_get_pnames)
{
    LLINT_BEGIN();
    JSValue v = LLINT_OP(2).jsValue();


	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition;
    if (v.isUndefinedOrNull()) 
      __b_condition = true;
    else
      __b_condition = false;
//WTF::dataFile().print("(", location, ") get_pnames\n");


//	Iter->count_idx++;
//	unsigned hash = exec->codeBlock()->hash().hash();				\
//
//        LLINT_CHECK_EXCEPTION();                                  
//
//	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_get_pnames) - 1].u.operand) - begin;
//  unsigned int fallthru = (pc + OPCODE_LENGTH(op_get_pnames)) - begin;
//
//WTF::dataFile().print("\tcond:", __b_condition, " taken:", taken, " fallthru:", fallthru, "\n");
//
//	if (Iter->isRegisteredBranch(location, hash)) 	 
//	{
//		std::vector<ExecutedBranch>::iterator it = Iter->e.switchedBranch.begin();
//		for (; it != Iter->e.switchedBranch.end(); it++)
//			if (it->count == Iter->count_idx)		// need switching
//			{
//        // break due to unexpected next branch
//			  if (it->addr != location || it->hash != hash)   
//			  {
//			    exec->codeBlock()->dumpStateSeparation(exec, it->count, location, it->addr, it->hash);
//		      it = Iter->e.switchedBranch.end();
//			    break;
//			  }
//
//        // follow up give switched target
////				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
//				Iter->updateBranchTarget(location, it->target, exec->codeBlock()->hash().hash());
//				pc = begin + it->target;
//				break;
//			}
//
//		if (it == Iter->e.switchedBranch.end())
//		{
//			if (__b_condition)                                        
//			{
//			  int offset = pc[OPCODE_LENGTH(op_get_pnames) - 1].u.operand;
//
//        // handling infinite loop
//			  if (offset<0) 
//			  {
//			    INFINITE_LOOP(op_get_pnames);
//			  }
//
////				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
//				Iter->updateBranchTarget(location, taken, exec->codeBlock()->hash().hash());
//				pc += offset;       
//			}
//			else
//			{
//        JSObject* o = v.toObject(exec);
//        Structure* structure = o->structure();
//        JSPropertyNameIterator* jsPropertyNameIterator = structure->enumerationCache();
//        if (!jsPropertyNameIterator || jsPropertyNameIterator->cachedPrototypeChain() != structure->prototypeChain(exec))
//            jsPropertyNameIterator = JSPropertyNameIterator::create(exec, o);
//        
//        LLINT_OP(1) = JSValue(jsPropertyNameIterator);
//        LLINT_OP(2) = JSValue(o);
//        LLINT_OP(3) = Register::withInt(0);
//        LLINT_OP(4) = Register::withInt(jsPropertyNameIterator->size());
//
////				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
//				Iter->updateBranchTarget(location, fallthru, exec->codeBlock()->hash().hash());
//				pc += OPCODE_LENGTH(op_get_pnames);                         
//			}
//		}
//	}
//	else		// This branch is not registered yet
//	{
//    if (__b_condition)                                        
//		{
////			exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
//			Iter->newBranch(location, taken, fallthru, exec->codeBlock()->hash().hash());
//   		pc += pc[OPCODE_LENGTH(op_get_pnames) - 1].u.operand;       
//		}
//   	else                                                      
//		{
//      JSObject* o = v.toObject(exec);
//      Structure* structure = o->structure();
//      JSPropertyNameIterator* jsPropertyNameIterator = structure->enumerationCache();
//      if (!jsPropertyNameIterator || jsPropertyNameIterator->cachedPrototypeChain() != structure->prototypeChain(exec))
//          jsPropertyNameIterator = JSPropertyNameIterator::create(exec, o);
//      
//      LLINT_OP(1) = JSValue(jsPropertyNameIterator);
//      LLINT_OP(2) = JSValue(o);
//      LLINT_OP(3) = Register::withInt(0);
//      LLINT_OP(4) = Register::withInt(jsPropertyNameIterator->size());
//
////			exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
//			Iter->newBranch(location, fallthru, taken, exec->codeBlock()->hash().hash());
//   		pc += OPCODE_LENGTH(op_get_pnames);                         
//		}
//	}


    if (v.isUndefinedOrNull()) {
        pc += pc[5].u.operand;
        LLINT_END();
    }
  
    JSObject* o = v.toObject(exec);
    Structure* structure = o->structure();
    JSPropertyNameIterator* jsPropertyNameIterator = structure->enumerationCache();
    if (!jsPropertyNameIterator || jsPropertyNameIterator->cachedPrototypeChain() != structure->prototypeChain(exec))
        jsPropertyNameIterator = JSPropertyNameIterator::create(exec, o);
    
    LLINT_OP(1) = JSValue(jsPropertyNameIterator);
    LLINT_OP(2) = JSValue(o);
    LLINT_OP(3) = Register::withInt(0);
    LLINT_OP(4) = Register::withInt(jsPropertyNameIterator->size());
    
    pc += OPCODE_LENGTH(op_get_pnames);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_next_pname)
{
    LLINT_BEGIN();

    JSObject* base = asObject(LLINT_OP(2).jsValue());
    JSString* property = asString(LLINT_OP(1).jsValue());

	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  bool __b_condition = base->hasProperty(exec, Identifier(exec, property->value(exec)));
//WTF::dataFile().print("(", location, ") next_pname\n");


//	Iter->count_idx++;
//	unsigned hash = exec->codeBlock()->hash().hash();				\
//
//        LLINT_CHECK_EXCEPTION();                                  
//
//	unsigned int taken = (pc + pc[OPCODE_LENGTH(op_next_pname) - 1].u.operand) - begin;
//  unsigned int fallthru = (pc + OPCODE_LENGTH(op_next_pname)) - begin;
//
//	if (Iter->isRegisteredBranch(location, hash)) 	 
//	{
//		std::vector<ExecutedBranch>::iterator it = Iter->e.switchedBranch.begin();
//		for (; it != Iter->e.switchedBranch.end(); it++)
//			if (it->count == Iter->count_idx)		// need switching
//			{
//        // break due to unexpected next branch
//			  if (it->addr != location || it->hash != hash)   
//			  {
//			    exec->codeBlock()->dumpStateSeparation(exec, it->count, location, it->addr, it->hash);
//		      it = Iter->e.switchedBranch.end();
//			    break;
//			  }
//
//        // follow up give switched target
////				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, it->target);
//				Iter->updateBranchTarget(location, it->target, exec->codeBlock()->hash().hash());
//				pc = begin + it->target;
//				break;
//			}
//
//		if (it == Iter->e.switchedBranch.end())
//		{
//			if (__b_condition)                                        
//			{
//			  int offset = pc[OPCODE_LENGTH(op_next_pname) - 1].u.operand;
//
//        // handling infinite loop
//			  if (offset<0) 
//			  {
//			    INFINITE_LOOP(op_next_pname);
//			  }
//
////				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
//				Iter->updateBranchTarget(location, taken, exec->codeBlock()->hash().hash());
//				pc += offset;       
//			}
//			else
//			{
////				exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
//				Iter->updateBranchTarget(location, fallthru, exec->codeBlock()->hash().hash());
//				pc += OPCODE_LENGTH(op_next_pname);                         
//			}
//		}
//	}
//	else		// This branch is not registered yet
//	{
//    if (__b_condition)                                        
//		{
////			exec->codeBlock()->dumpDynamicFlowGraph(pc,location, taken);
//			Iter->newBranch(location, taken, fallthru, exec->codeBlock()->hash().hash());
//   		pc += pc[OPCODE_LENGTH(op_next_pname) - 1].u.operand;       
//		}
//   	else                                                      
//		{
////			exec->codeBlock()->dumpDynamicFlowGraph(pc,location, fallthru);
//			Iter->newBranch(location, fallthru, taken, exec->codeBlock()->hash().hash());
//   		pc += OPCODE_LENGTH(op_next_pname);                         
//		}
//	}


    LLINT_BRANCH2(op_next_pname, base->hasProperty(exec, Identifier(exec, property->value(exec))));		// kt
    if (base->hasProperty(exec, Identifier(exec, property->value(exec)))) {
        // Go to target.
        pc += pc[6].u.operand;
    } // Else, don't change the PC, so the interpreter will reloop.
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_push_with_scope)
{
    LLINT_BEGIN();
    JSValue v = LLINT_OP_C(1).jsValue();
    JSObject* o = v.toObject(exec);
    LLINT_CHECK_EXCEPTION();
    
    exec->setScope(JSWithScope::create(exec, o));
    
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_pop_scope)
{
    LLINT_BEGIN();
    exec->setScope(exec->scope()->next());
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_push_name_scope)
{
    LLINT_BEGIN();
    CodeBlock* codeBlock = exec->codeBlock();
    JSNameScope* scope = JSNameScope::create(exec, codeBlock->identifier(pc[1].u.operand), LLINT_OP(2).jsValue(), pc[3].u.operand);
    exec->setScope(scope);
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_throw)
{
    LLINT_BEGIN();
  // kt
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
  WTF::dataFile().print("(", location, ")", "throw\n");

  // kt
    static unsigned int throwCount = 0;
    static std::set<std::pair<unsigned int, int> > throwSet;
    std::set<std::pair<unsigned int, int> >::iterator it = throwSet.find(std::make_pair(exec->codeBlock()->hash().hash(), location));
    if (it == throwSet.end())
    {
      throwCount++;
      throwSet.insert(std::make_pair(exec->codeBlock()->hash().hash(), location));

      // finding relevant EH
      HandlerInfo* handler = exec->codeBlock()->handlerForBytecodeOffset(location);
//      JSValue value = vm.exception();
//      HandlerInfo* handler = vm.interpreter->unwind(exec, value);
//      
//      HandlerInfo* handler = 0;
//      CodeBlock *codeBlock = exec->codeBlock();
//      bool istermination = false;
//      UnwindFunctor functor(*(&exec), istermination, codeBlock, handler);
//      exec->iterate(functor);

      if (handler)
        WTF::dataFile().print("\tthrowCount(catched) ", throwCount, "\n");
      else
        WTF::dataFile().print("\tthrowCount(uncatched) ", throwCount, "\n");
    }

    pc += OPCODE_LENGTH(op_throw);                         
    LLINT_END_IMPL();                                        

//    LLINT_THROW(LLINT_OP_C(1).jsValue());
}

LLINT_SLOW_PATH_DECL(slow_path_throw_static_error)
{
    LLINT_BEGIN();
    if (pc[2].u.operand)
        LLINT_THROW(createReferenceError(exec, errorDescriptionForValue(exec, LLINT_OP_C(1).jsValue())->value(exec)));
    else
        LLINT_THROW(createTypeError(exec, errorDescriptionForValue(exec, LLINT_OP_C(1).jsValue())->value(exec)));
}

LLINT_SLOW_PATH_DECL(slow_path_handle_watchdog_timer)
{
    LLINT_BEGIN_NO_SET_PC();
    ASSERT(vm.watchdog);
    if (UNLIKELY(vm.watchdog->didFire(exec)))
        LLINT_THROW(createTerminatedExecutionException(&vm));
    LLINT_RETURN_TWO(0, exec);
}

LLINT_SLOW_PATH_DECL(slow_path_debug)
{
    LLINT_BEGIN();
    int debugHookID = pc[1].u.operand;
    vm.interpreter->debug(exec, static_cast<DebugHookID>(debugHookID));
    
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_profile_will_call)
{
    LLINT_BEGIN();
    if (LegacyProfiler* profiler = vm.enabledProfiler())
        profiler->willExecute(exec, LLINT_OP(1).jsValue());
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_profile_did_call)
{
    LLINT_BEGIN();
    if (LegacyProfiler* profiler = vm.enabledProfiler())
        profiler->didExecute(exec, LLINT_OP(1).jsValue());
    LLINT_END();
}

LLINT_SLOW_PATH_DECL(slow_path_handle_exception)
{
    LLINT_BEGIN_NO_SET_PC();
    ASSERT(vm.exception());
    genericUnwind(&vm, exec, vm.exception());
    LLINT_END_IMPL();
}

LLINT_SLOW_PATH_DECL(slow_path_resolve_scope)
{
    LLINT_BEGIN();
    const Identifier& ident = exec->codeBlock()->identifier(pc[2].u.operand);
    LLINT_RETURN(JSScope::resolve(exec, exec->scope(), ident));
}

LLINT_SLOW_PATH_DECL(slow_path_get_from_scope)
{
    LLINT_BEGIN();
	Instruction *begin = exec->codeBlock()->instructions().begin();
	unsigned int location = pc - begin;				
    const Identifier& ident = exec->codeBlock()->identifier(pc[3].u.operand);
// kt 
//    Identifier ident = exec->codeBlock()->identifier(pc[3].u.operand);
//	Identifier id(exec, "XMLHttpRequest");	// 
//	if (ident.equal(ident.impl(), "ActiveXObject"))
//		ident = id;

    JSObject* scope = jsCast<JSObject*>(LLINT_OP(2).jsValue());
    ResolveModeAndType modeAndType(pc[4].u.operand);

// kt
//scope->dump(WTF::dataFile());
//temp = scope;
//exec->codeBlock()->lastGetFromScope = ident;


    PropertySlot slot(scope);
    if (!scope->getPropertySlot(exec, ident, slot)) {
        if (modeAndType.mode() == ThrowIfNotFound)
          // kt only for ThrowIfNotFound
        {
	          Identifier id(exec, "chrome");	 

            // get_from_scope ("chrome")
	          PropertySlot slot2(exec->codeBlock()->globalObject());
            exec->codeBlock()->globalObject()->getPropertySlot(exec, id, slot2);
	          JSValue chrome = slot2.getValue(exec, id);

	          // put_to_scope 
            PutPropertySlot slot3(scope, exec->codeBlock()->isStrictMode());
            scope->methodTable()->put(scope, exec, ident, chrome, slot3);

	          // put to shadow
//            shadow[std::make_pair(scope, ident.utf8())] = chrome;

            // again
            scope->getPropertySlot(exec, ident, slot);
//            LLINT_RETURN(exec->vm().throwException(exec, createUndefinedVariableError(exec, ident)));
        }
        else
          LLINT_RETURN(jsUndefined());
    }

    // Covers implicit globals. Since they don't exist until they first execute, we didn't know how to cache them at compile time.
    if (slot.isCacheableValue() && slot.slotBase() == scope && scope->structure()->propertyAccessesAreCacheable()) {
        if (modeAndType.type() == GlobalProperty || modeAndType.type() == GlobalPropertyWithVarInjectionChecks) {
            CodeBlock* codeBlock = exec->codeBlock();
            ConcurrentJITLocker locker(codeBlock->m_lock);
            pc[5].u.structure.set(exec->vm(), codeBlock->ownerExecutable(), scope->structure());
            pc[6].u.operand = slot.cachedOffset();
        }
    }

    // kt ... shadow_object
//    if (slot.getValue(exec, ident).isUndefined())
//    {
//  		std::map<std::pair<JSObject*, CString>, String>::iterator it = shadow_object.find(std::make_pair(scope, ident.impl()->utf8()));	
//		  if (it != shadow_object.end())
//		  {
//        JSValue baseValue;
//	      Identifier id(exec, it->second);	
//
//	      PropertySlot slot2(scope);
//    	  scope->getPropertySlot(exec, id, slot2);
//	      JSValue calleeAsValue = slot2.getValue(exec, id);
//
//        CONSTRUCTOR();
//
//        LLINT_RETURN(baseValue);
//      }
//        
//    }

    LLINT_RETURN(slot.getValue(exec, ident));
}

LLINT_SLOW_PATH_DECL(slow_path_put_to_scope)
{
    LLINT_BEGIN();
    CodeBlock* codeBlock = exec->codeBlock();
    const Identifier& ident = codeBlock->identifier(pc[2].u.operand);
    JSObject* scope = jsCast<JSObject*>(LLINT_OP(1).jsValue());
    JSValue value = LLINT_OP_C(3).jsValue();
    ResolveModeAndType modeAndType = ResolveModeAndType(pc[4].u.operand);

    if (modeAndType.mode() == ThrowIfNotFound && !scope->hasProperty(exec, ident))
        LLINT_THROW(createUndefinedVariableError(exec, ident));

    PutPropertySlot slot(scope, codeBlock->isStrictMode());
    scope->methodTable()->put(scope, exec, ident, value, slot);

    // Covers implicit globals. Since they don't exist until they first execute, we didn't know how to cache them at compile time.
    if (modeAndType.type() == GlobalProperty || modeAndType.type() == GlobalPropertyWithVarInjectionChecks) {
        if (slot.isCacheablePut() && slot.base() == scope && scope->structure()->propertyAccessesAreCacheable()) {
            ConcurrentJITLocker locker(codeBlock->m_lock);
            pc[5].u.structure.set(exec->vm(), codeBlock->ownerExecutable(), scope->structure());
            pc[6].u.operand = slot.cachedOffset();
        }
    }

    LLINT_END();
}

extern "C" SlowPathReturnType llint_throw_stack_overflow_error(VM* vm, ProtoCallFrame* protoFrame)
{
    ExecState* exec = vm->topCallFrame;
    if (!exec)
        exec = protoFrame->scope()->globalObject()->globalExec();
    throwStackOverflowError(exec);
    return encodeResult(0, 0);
}

#if !ENABLE(JIT)
extern "C" SlowPathReturnType llint_stack_check_at_vm_entry(VM* vm, Register* newTopOfStack)
{
    bool success = vm->interpreter->stack().ensureCapacityFor(newTopOfStack);
    return encodeResult(reinterpret_cast<void*>(success), 0);
}
#endif

extern "C" void llint_write_barrier_slow(ExecState* exec, JSCell* cell)
{
    VM& vm = exec->vm();
    vm.heap.writeBarrier(cell);
}

extern "C" NO_RETURN_DUE_TO_CRASH void llint_crash()
{
    CRASH();
}

} } // namespace JSC::LLInt
