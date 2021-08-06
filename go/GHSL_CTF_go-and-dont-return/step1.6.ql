import go

// ======
// Step 1.6: Putting it all together
// ======

from Ident i, EqualityTestExpr e, IfStmt s
where  i.getName()="ErrNone" and
    e.getRightOperand() = i and 
    s.getCond() = e // official expected answer
    // s.getCond().getAChild*() = e // more precisous than ctf expect
    and not exists(ReturnStmt r|s.getThen().getAStmt*() = r)
select i,s.getLocation()