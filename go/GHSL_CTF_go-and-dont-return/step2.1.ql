import go

// Step 2.1: Find conditionals that are fed from calls to isReqAuthenticated

class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "Step 2.1: Find conditionals that are fed from calls to isReqAuthenticated" }
    override predicate isSource(DataFlow::Node source) {
        source = any(Function f|f.hasQualifiedName("github.com/minio/minio/cmd", "isReqAuthenticated")).getACall()
    }
    override predicate isSink(DataFlow::Node sink){
        exists(DataFlow::EqualityTestNode e|
            sink = e.getAnOperand()
        )
    }
}

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select source, sink, sink.getNode().asExpr().getLocation()