import go

// ======
// Step 1.3: Finding if-blocks making such a test
// ======

from Ident i, EqualityTestExpr e, IfStmt s
where i.getName()="ErrNone" and
    e.getRightOperand() = i and 
    s.getCond() = e // official expected answer
    // s.getCond().getAChild*() = e // more precisous than ctf expect
select i,s.getLocation()