import go

// Step 2.2: Find the true bug!

predicate isEqualityTestAgainstErrNodeWithoutReturnInThen(EqualityTestExpr e) {
    exists(Ident i, IfStmt s | i.getName() = "ErrNone" and
        e.getAnOperand() = i and
        s.getCond() = e
        // s.getCond().getAChild*() = e
        and not exists(ReturnStmt r|s.getThen().getAChild*() = r)
    )
}

class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "Step 2.2: Find the true bug!" }
    override predicate isSource(DataFlow::Node source) {
        source = any(Function f|f.hasQualifiedName("github.com/minio/minio/cmd", "isReqAuthenticated")).getACall()
    }
    override predicate isSink(DataFlow::Node sink){
        exists(DataFlow::EqualityTestNode e|
            sink = e.getAnOperand() and
            isEqualityTestAgainstErrNodeWithoutReturnInThen(e.asExpr())
        )
    }
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select source, sink, sink.getNode().asExpr().getLocation()