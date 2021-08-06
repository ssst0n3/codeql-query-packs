import go

// ======
// Step 1.2: Finding equality tests against ErrNone
// ======
 
from Ident i, EqualityTestExpr e
where i.getName()="ErrNone" and
    e.getRightOperand() = i
select i, e, i.getLocation()