/**
 * @description Find functions directly called by tests
 * @kind problem
 * @id javascript/functions-directly-called-by-tests
 * @problem.severity recommendation
 */
import javascript

/**
 * Holds if a function is a test.
 */
predicate isTest(Function test) {
  exists(CallExpr describe, CallExpr it |
    describe.getCalleeName() = "describe" and
    it.getCalleeName() = "it" and
    it.getParent*() = describe and
    test = it.getArgument(1)
  )
}

/**
* Holds if `caller` contains a call to `callee`.
*/
predicate calls(Function caller, Function callee) {
  exists(DataFlow::CallNode call |
    call.getEnclosingFunction() = caller and
    call.getACallee() = callee
  )
}

/**
 * Holds if the given function is a public method of a class.
 */
predicate isPublicMethod(Function f) {
  exists(MethodDefinition md | md.isPublic() and md.getBody() = f)
}

/**
* Holds if the given function is exported from a module.
*/
predicate isExportedFunction(Function f) {
  exists(Module m | m.getAnExportedValue(_).getAFunctionValue().getFunction() = f) and
  not f.inExternsFile()
}

/**
* Holds if the given function is not greater than 10 lines.
*/ 
predicate isTooLong(Function f) {
  exists(MethodDefinition md | 
  md.getNumLines() <= 10)
}

/**
* Finds all public methods not called by tests.
*/
predicate isPublicNoTests(Function f) {
  exists(MethodDefinition md |
  md.isPublic() and !md.isTest())
}

from Function test, Function callee
where isTest(test) and
      calls(test, callee)
select callee, "is directly called by a test"