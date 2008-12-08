
-- This function saturates an integer lattice. It expects 
-- the matrix A, whose image is the lattice. 
Lsat = (A) -> gens ker transpose gens ker transpose A;
pp = (I) -> ( 
     print I;
     print ring I;
     )

