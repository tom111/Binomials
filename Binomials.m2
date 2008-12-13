R = QQ[x1,x2,x3,x4,x5]
I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6)
-- Here is a cellular decomp  of I:
J1 = ideal({x1^2 , x1*x4^2 - x2*x5^2, x2^5, x5^6, x2^4 * x4^2,x4^8})
J2 = ideal({x1*x4^2 - x2*x5^2, x1^3*x3^3 - x4^2*x2^4, x2^3*x4^4 - x1^2*x3^3*x5^2, x2^2*x4^6 - x1*x3^3*x5^4, x2*x4^8 - x3^3 *x5^6 })

axisSaturate = (I,i) -> (
-- By Ignacio Ojeda and Mike Stillman
-- For computing saturations w.r.t. a single variable:
    R := ring I;
    I1 := ideal(1_R);
    s = 0;
    f = R_i;
    while not(I1 == I) do (
	s = s + 1;
	I1 = I;
	I = ideal syz gb(matrix{{f}}|gens I,
            SyzygyRows=>1,Syzygies=>true););
    {s-1, I}
    )

-- Cellular decomposition of binomial ideals:
--

binomialCD = (I) -> (
-- By Ignacio Ojeda and Mike Stillman     
     R := ring I;
     n := numgens R;
     Answer = {};
     IntersectAnswer = ideal(1_R);
     ToDo = {{1_R,toList(0..n-1),I}};
     compo = 0;
     next = () -> (
	 if #ToDo === 0 then false
	 else (
	      L = ToDo#0;
	      ToDo = drop(ToDo,1);
	      if gens IntersectAnswer % L#2 == 0
	      then (<< "redundant component" << endl;)
	      else if #(L#1) === 0 then (
		   -- We have an answer
                   compo = compo + 1; 
		   newone := trim L#2;
		   << "component: " << {compo, gens newone} << endl;
		   Answer = append(Answer,newone);
		   IntersectAnswer = intersect(IntersectAnswer,newone);
		   if IntersectAnswer == I then ToDo = {})
	      else (
	           i := L#1#0;
		   newL1 = drop(L#1,1);
	           result = axisSaturate(L#2, i);
		   J := result#1;
		   k := result#0;
		   if k > 0 then (
			J2 = L#2 + ideal(R_i^k);
			-- We need to remove any components supported on the first vars
			J2 = saturate(J2, L#0);
			if J2 != ideal(1_R) then
			    ToDo = prepend({L#0, newL1, J2},ToDo));
		   if J != ideal(1_R) then ToDo = prepend({R_i * L#0, newL1, J},ToDo);
		   );
	      true));
     while next() do ();
     Answer	      
     )

-- This function saturates an integer lattice. It expects 
-- the matrix A, whose image is the lattice. 
Lsat = (A) -> gens ker transpose gens ker transpose A;

partialCharacter = (I) -> (
     vs := {};
     cl := {};
     -- The partial Character of the zero ideal is the 
     -- zero lattice.       
     if ( I == 0 ) then (
	  for i in gens ring I do vs = vs | { 0 };
	  cl = {1};
	  return (transpose matrix {vs}, cl);
	  );
     ts := entries gens I;
     for t in ts#0 do (
	  if t != 0 then (
	       vs = vs | {((exponents (t))#0 - (exponents (t))#1)};
     	       coeffs := entries ((coefficients(t))#1);
	       -- I hope that coefficients returns the leading coeff as 0th
	       cl = cl | { -coeffs#1#0 / coeffs#0#0}
	       );
	  );
--    print coeffs;
--    print cl;
     return (transpose matrix vs , cl);
     )

cellVars = (I) -> (
     cv = {};
     for i in gens ring I do if saturate (I,i) != substitute(ideal(1), ring I) then cv=cv|{i};
     return cv;
     )

nonCellstdm = (I) -> (
     R := ring I;
     cv := set(cellVars(I)); 
     -- Here go the non-cell variables
     ncv := toList(set (gens R) - cv);
     -- We project I to the non-cell variables
     Q := QQ[ncv];
     projnE := map (Q,R);
     J := projnE I;
     S = Q/J;
     slist = entries flatten basis (S);
     use R;
     return slist;
     )
  
BinassPrim = (I) -> (
     R := ring I;
     ml := nonCellstdm(I);
     cv := cellVars(I);
     ncv := toList(set (gens R) - cv);
     Q := QQ[cv];
     use R;
     for m in ml do (
	  print " "
	  )
     )   
     

-- Saturierungsalgorithmus fuer partielle Charactere 
-- 1. Matrix Saturieren
-- 2. zufaellig probieren bis man eine quadratische 
--    Submatrix von vollem Rang gefunden hat


--saturatepChar = (ch) -> (
--     mat := Lsat(ch#0);
--     rg := rank mat;
--     rows := toList ( 0..((numrows mat) -1) );
--     
--     currows = for i in 0..rg-1 list rows#i;
--     while determinant submatrix (mat, currows ) == 0 (
--	  rows = random(rows);
--	  currows = for i in 0..rg-1 list rows#i;
--	  )
--     submat;
--     )
