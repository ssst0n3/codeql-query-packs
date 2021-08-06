import cpp

string getPostfix(Expr f) {
    result = f.getFile().toString() + ":L" + f.getLocation().getStartLine()
}

// ======
// Question 0.0: alloca is a macro. Find the definition of this macro and the name of the function that it expands to.
// 
// get __libc_use_alloca
// ======

// from Macro m 
// where m.getName() = "alloca"
// select m, m.getFile().toString()

// ======
// Question 1.0: Find all the calls to alloca (using the function name that you found in step 0).
// ======

// from FunctionCall fc 
// where fc.getTarget().hasQualifiedName("__libc_use_alloca")
// select fc, getPostfix(fc)

// ======
// Question 1.1: Use the upperBound and lowerBound predicates from the SimpleRangeAnalysis library to filter out results 
// which are safe because the allocation size is small. You can classify the allocation size as small if it is less than 65536. 
// But don't forget that negative sizes are very dangerous.
// ======

import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis

predicate isInValidRangeAllocaCall(FunctionCall allocaCall) {
    exists(|allocaCall.getTarget().hasQualifiedName("__builtin_alloca") and
        (
            upperBound(allocaCall.getArgument(0).getFullyConverted()) >= 65536 or
            lowerBound(allocaCall.getArgument(0).getFullyConverted()) < 0
        )
    )
}

// from FunctionCall fc
// where isInValidRangeAllocaCall(fc)
// select fc, getPostfix(fc)

// ======
// Question 2.0: Find all calls to __libc_use_alloca
// ======

// from FunctionCall fc 
// where fc.getTarget().hasQualifiedName("__libc_use_alloca")
// select fc, getPostfix(fc)

// ======
// Question 2.1: Find all guard conditions where the condition is a call to __libc_use_alloca
// ======

// import semmle.code.cpp.controlflow.Guards

// predicate isAllocaCallGuardedBy__libc_use_allocaDirectly(FunctionCall allocaCall) {
//     exists(FunctionCall fc,GuardCondition gc|allocaCall.getTarget().hasQualifiedName("__builtin_alloca") and
//         fc.getTarget().hasQualifiedName("__libc_use_alloca") and
//         gc.controls(allocaCall.getBasicBlock(), _) and
//         gc.getAChild*() = fc
//     )
// }

// from FunctionCall fc
// where isAllocaCallGuardedBy__libc_use_allocaDirectly(fc)
// select fc, getPostfix(fc)

// ======
// Question 2.2: Sometimes the result of __libc_use_alloca is assigned to a variable, 
// which is then used as the guard condition. For example, this happens at setsourcefilter.c:38-41. 
// Enhance your query, using local dataflow, so that it also finds this guard condition.
// ======

// import semmle.code.cpp.controlflow.Guards
// import semmle.code.cpp.dataflow.DataFlow

// predicate isAllocaCallGuardedBy__libc_use_allocaEnhance(GuardCondition gc) {
//     exists(FunctionCall allocaCall,FunctionCall fc,DataFlow::Node source, DataFlow::Node sink|
//         allocaCall.getTarget().hasQualifiedName("__builtin_alloca") and
//         fc.getTarget().hasQualifiedName("__libc_use_alloca") and
//         gc.controls(allocaCall.getBasicBlock(), _) and
//         DataFlow::localFlow(source, sink) and
//         source.asExpr() = fc and
//         sink.asExpr() = gc
//     )
// }

// from GuardCondition gc
// where isAllocaCallGuardedBy__libc_use_allocaEnhance(gc)
// select gc, getPostfix(gc)

// ======
// Question 2.3: Sometimes the call to __libc_use_alloca is wrapped in a call to __builtin_expect. 
// For example, this happens at setenv.c:185. Enhance your query so that it also finds this guard condition.
//
// add 1 result: setenv.c
// ======

// import semmle.code.cpp.controlflow.Guards
// import semmle.code.cpp.dataflow.DataFlow

// predicate isAllocaCallGuardedBy__libc_use_allocaEnhance__builtin_expect(GuardCondition gc) {
//     exists(FunctionCall allocaCall,FunctionCall fc,DataFlow::Node source, DataFlow::Node sink|
//         allocaCall.getTarget().hasQualifiedName("__builtin_alloca") and
//         fc.getTarget().hasQualifiedName("__libc_use_alloca") and
//         gc.controls(allocaCall.getBasicBlock(), _) and
//         DataFlow::localFlow(source, sink) and
//         source.asExpr() = fc and
//         sink.asExpr() = gc.getAChild*()
//     )
// }

// from GuardCondition gc
// where isAllocaCallGuardedBy__libc_use_allocaEnhance__builtin_expect(gc)
// select gc, getPostfix(gc)

// ======
// Question 2.4: Sometimes the result of __libc_use_alloca is negated with the ! operator. 
// For example, this happens at getaddrinfo.c:2291-2293. 
// Enhance your query so that it can also handle negations. 
// 
// Add result: x=!__libc_use_alloca
// ======

// import semmle.code.cpp.controlflow.Guards
// import semmle.code.cpp.dataflow.DataFlow

// predicate isAllocaCallGuardedBy__libc_use_allocaEnhance__builtin_expectWithNegations(GuardCondition gc) {
//     exists(FunctionCall allocaCall,FunctionCall fc,DataFlow::Node source, DataFlow::Node sink, BasicBlock block|
//         allocaCall.getTarget().hasQualifiedName("__builtin_alloca") and
//         fc.getTarget().hasQualifiedName("__libc_use_alloca") and
//         gc.controls(allocaCall.getBasicBlock(), _) and
//         DataFlow::localFlow(source, sink) and
//         block.contains(fc) and
//         source.asExpr() = block.getANode() and
//         sink.asExpr() = gc.getAChild*()
//     )
// }

// from GuardCondition gc
// where isAllocaCallGuardedBy__libc_use_allocaEnhance__builtin_expectWithNegations(gc)
// select gc, getPostfix(gc)

// ======
// Question 2.5: Find calls to alloca that are safe because they are guarded 
// by a call to __libc_use_alloca
// ======

import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

predicate isSafeAllocaCall(FunctionCall allocaCall) {
    exists(FunctionCall fc, DataFlow::Node source, DataFlow::Node sink, GuardCondition guard, BasicBlock block |
        allocaCall.getTarget().hasQualifiedName("__builtin_alloca") and
        fc.getTarget().hasQualifiedName("__libc_use_alloca") and
        guard.controls(allocaCall.getBasicBlock(), _) and 
        DataFlow::localFlow(source, sink) and
        block.contains(fc) and
        source.asExpr() = block.getANode() and
        sink.asExpr() = guard.getAChild*()
    )
}

// from FunctionCall fc
// where isSafeAllocaCall(fc)
// select fc, "is safe __alloca() call", getPostfix(fc)

// ======
// Question 3.0: use your answer from step 2 to enhance your query from step 1 by 
// filtering out calls to alloca that are safe because they are guarded by a call to __libc_use_alloca.
// ======

// from FunctionCall fc
// where isInValidRangeAllocaCall(fc)
//     // and not isSafeAllocaCall(fc)
// select fc, getPostfix(fc)

// ======
// Question 4.0: Find calls to fopen. (Be aware that fopen is another macro.)
// 
// define fopen(fname, mode) _IO_new_fopen (fname, mode)
// ======

// from Macro m
// where m.getName()="fopen"
// select m

// from FunctionCall fc
// where fc.getTarget().getQualifiedName()="_IO_new_fopen"
// select fc, getPostfix(fc)

// ======
// Question 4.1: Write a taint tracking query. 
// The source should be a call to fopen and the sink should be the size argument of an unsafe call to alloca.
// ======

import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.models.interfaces.DataFlow
import semmle.code.cpp.controlflow.Guards
import DataFlow::PathGraph

// Track taint through `__strnlen`.
class StrlenFunction extends DataFlowFunction {
    StrlenFunction() { this.getName().matches("%str%len%") }
  
    override predicate hasDataFlow(FunctionInput i, FunctionOutput o) {
      i.isInParameter(0) and o.isOutReturnValue()
    }
  }
  
  // Track taint through `__getdelim`.
  class GetDelimFunction extends DataFlowFunction {
    GetDelimFunction() { this.getName().matches("%get%delim%") }
  
    override predicate hasDataFlow(FunctionInput i, FunctionOutput o) {
      i.isInParameter(3) and o.isOutParameterPointer(0)
    }
  }
  
  class Config extends TaintTracking::Configuration {
    Config() { this = "fopen_to_alloca_taint" }
  
    override predicate isSource(DataFlow::Node source) {
        exists(FunctionCall fc, BasicBlock block|
            fc.getTarget().getQualifiedName() = "_IO_new_fopen" and
            block.contains(fc) and
            source.asExpr() = block.getANode()
        )
    }
  
    override predicate isSink(DataFlow::Node sink) {
        exists(FunctionCall fc, BasicBlock block|
            not isSafeAllocaCall(fc) and
            isInValidRangeAllocaCall(fc) and
            block.contains(fc) and
            sink.asExpr() = block.getANode() and
            sink.asExpr() = fc.getArgument(0).getFullyConverted()
        )
    }
  }
  
  from Config cfg, DataFlow::PathNode source, DataFlow::PathNode sink
  where cfg.hasFlowPath(source, sink)
  select sink, source, "fopen flows to alloca", sink.getNode().getLocation().getFile()