import go

// ======
// Step 1.1: Finding references to ErrNone
// ======
 
from Ident i
where i.getName()="ErrNone"
select i, i.getLocation()