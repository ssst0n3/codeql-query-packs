import go

// ======
// Step 1.5: Finding if-blocks without return statements
// ======

from IfStmt s
where not exists(ReturnStmt r|s.getThen().getAStmt*() = r)
select s,s.getLocation()