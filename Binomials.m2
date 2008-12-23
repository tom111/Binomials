-- R = QQ[x1,x2,x3,x4,x5]
-- I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6)
-- -- Here is a cellular decomp  of I:
-- -- This is also a prime decomposition
-- J1 = ideal({x1^2 , x1*x4^2 - x2*x5^2, x2^5, x5^6, x2^4 * x4^2,x4^8})
-- J2 = ideal({x1*x4^2 - x2*x5^2, x1^3*x3^3 - x4^2*x2^4, x2^3*x4^4 - x1^2*x3^3*x5^2, x2^2*x4^6 - x1*x3^3*x5^4, x2*x4^8 - x3^3 *x5^6 })
-- 
-- 
-- Q = QQ[x,y,z]
-- J = ideal(x^4*y^2-z^6,x^3*y^2-z^5,x^2-y*z)
-- The cellular decomposition is also a primary decomposition.
-- No lattice needs to be saturated, only roots of monomials

-- R = QQ[a,b,c]
-- I = ideal(a-b^5,a^2-c,b^2-c^3,c^2-a*b)
 
-- Q = QQ[x,y,z,w]
-- J = ideal(x^4*w^2-z^6,x^3*y^2-z^5,x^7-y^3*w^2,x^2*x^3-z^7)
-- 
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
     vs := {}; -- This will hold the lattice generators
     vs2 := {};
     vsmat := matrix "0"; -- Holds the matrix whose image is L 
     cl := {}; -- This will hold the coefficients
     R := ring I;
          
     -- The input should be a cellular ideal 
     cellvars := cellVars(I);
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     CoeffR := coefficientRing R;
     S := CoeffR[cellvars];
     II := kernel map (R/I,S);

     -- The partial Character of the zero ideal is the 
     -- zero lattice.       
     if ( II == 0 ) then (
	  for i in gens ring II do vs = vs | { 0 };
	  cl = {1};
	  return (cellvars, transpose matrix {vs}, cl);
	  );
     
     -- So, II is not zero:
     -- Let ts be the list of generators
     ts := entries gens II;
     -- print ts;
     -- for each term, find the exponent vector
     oldmat := matrix "0";
     oldvs := {};
     for t in ts#0 do (
	  -- Want to check if we already have this generator included
	  
	  -- Save the old values
	  oldmat = vsmat;
	  oldvs = vs;
	  	  
	  -- compute new ones
	  -- print t;
	  -- print  {((exponents (t))#0 - (exponents (t))#1)};
	  vs = vs | {((exponents (t))#0 - (exponents (t))#1)};
	  -- print vs;
	  vsmat = transpose matrix vs;
	  
	  -- Do we need the new generator ?
	  if (image oldmat == image vsmat) then (
	       -- Undo changes:
	       vsmat = oldmat;
	       vs = oldvs;
	       )
	  else (
	       -- So we have a new generator : update coefficient list
	       coeffs := entries ((coefficients(t))#1);
               cl = cl | { -coeffs#1#0 / coeffs#0#0}
	       );
	  );
--    print coeffs;
--    print cl;
     
     -- back to the old ring
     use R;
     return (cellvars, transpose matrix vs , cl);
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

IdealfromCharacter = (R,A,c) -> (
     -- Constructs the Ideal I_+(c) in R
     -- R is a ring in which the ideal is returned
     -- The columns of A should contain exponent vectors of generators
     -- The vector c contains the corresponding coefficients which must lie
     --      in the coefficient ring of R !!!
     
     use R;
     
     -- We coerce the coefficients to R:
     c = apply (c, (a) -> (sub (a,R)));
      
     var := gens R;
     cols := entries transpose A;
     posmon := 1;
     negmon := 1;
     binomials := {};
     for i in (0..(numcols A)-1) do (
	  for j in (0..(numrows A)-1) do (
	       if cols#i#j > 0 then (
		    posmon = posmon * var#j^(cols#i#j)
		    )
	       else (
		    negmon = negmon * (var#j)^(-cols#i#j)
		    );
	       );
     	  binomials = binomials | {posmon - c#i * negmon};
	  posmon = 1;
	  negmon = 1;
	  );
     print ideal (binomials);
     -- If the coefficients are all "1". Can we use 4ti2 here?
     return saturate(ideal(binomials), product(var));
     )

-- How to do overloading ?	  
-- IdealfromCharacter = (R,A) -> (
--     c := {};
--     for i in (1..numcols A) do c = c | {1};
--     return IdealfromCharacter(R,A,c);
--     )
         
  
satpchar = ( A , c) -> (
     -- print A;
     -- print c;

     -- If the lattice is saturated, the character is saturated     
     if (image Lsat A == image A) then (
	  return (A,c);
	  );
     
     S := Lsat(A);
     K = A // S;
     
     sageprogfile := temporaryFileName() | ".sage";
     sageoutfile := temporaryFileName();
     -- We paste the whole program in:
     F := openOut(sageprogfile);
     
F << "S = matrix(ZZ,[";
-- Here goes the saturated lattice defining matrix
ent := entries S;
for r in (0..(#ent -1)) do (
     F << "[";
     for c in (0..(#(ent#r)-1)) do (
	  F << ent#r#c;
	  if (c < (numcols S) -1 ) then F << ",";
	  );
     F << "]";
     if (r < (numrows S) -1) then F << ",";
     );
F << "])" << endl;
     
F << "A = matrix(ZZ,[";
-- Here goes the lattice defining matrix
ent = entries A;
for r in (0..(#ent -1)) do (
     F << "[";
     for c in (0..(#(ent#r)-1)) do (
	  F << ent#r#c;
	  if (c < (numcols A) -1 ) then F << ",";
	  );
     F << "]";
     if (r < (numrows A) -1) then F << ",";
     );
F << "])" << endl;

F << "K = matrix(ZZ,[";
-- Here goes the coefficient matrix
ent = entries K;
for r in (0..(#ent -1)) do (
     F << "[";
     for c in (0..(#(ent#r)-1)) do (
	  F << ent#r#c;
	  if (c < (numcols K) -1 ) then F << ",";
	  );
     F << "]";
     if (r < (numrows K) -1) then F << ",";
     );
F << "])" << endl;

-- Here goes the character
F << "l = [";
for i in (0..((#c)-1)) do (
     F << c#i ;
     if (i< (#c -1)) then F << ",";
     );
F << "]" << endl;

-- The main program
F << "varnames = []" << endl;
F << "rg = len(S.columns())" << endl;
F << "for i in range(rg) :" << endl;
F << "    varnames = varnames + ['m'+str(i)]" << endl;
F << "for v in varnames:" << endl;
F << "    # print v" << endl;
F << "    var (v)" << endl;
F << "eqns = []" << endl;
F << "kr = len(K.rows())" << endl;
F << "kc = len(K.columns());" << endl;
F << "for col in range(kc):" << endl;
F << "    monom = 1" << endl;
F << "    for row in range(kr):" << endl;
F << "        monom *= eval('m'+str(row))^K[row,col]" << endl;
F << "        # print eval('m'+str(row))^K[row,col]" << endl;
F << "    eqns = eqns + [ monom - l[col] ]" << endl;
F << "satlist = [] # The list of saturations" << endl;
F << "vs = [eval(v) for v in varnames]" << endl;
F << "if (len (eqns) > 1) :" << endl;
F << "    s = solve (eqns , tuple(vs), solution_dict=True)" << endl;
F << "else :" << endl;
F << "    spre = solve (eqns , tuple(vs))" << endl;
F << "    # print spre" << endl;
F << "    s= [dict([(eq.left(),eq.right())]) for eq in spre ]" << endl;
F << "m = [] " << endl;
F << "for sol in s :" << endl;
F << "    n = [] " << endl;
F << "    for v in varnames:" << endl;
F << "        n = n + [sol[v]]" << endl;
F << "    m = m + [n]" << endl;

-- Here we do output
F << "charstr = str(m).replace('I','ii');" << endl;
F << "charstr = charstr.replace('[','{');" << endl;
F << "charstr = charstr.replace(']','}');" << endl;
F << "print 'c := ' + charstr" << endl;

     close (F);
     
     execstr = "sage "|sageprogfile | " > " | sageoutfile ;
     -- print execstr;
     ret := run (execstr);
     if (ret != 0) then (
	  print "sage did not run correctly, sorry :(";
	  return False;
	  );
     
     outlines = lines get sageoutfile;
     
     cl := value outlines#0;
     return (S,cl)
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
     
     
-- cd = binomialCD(J)
-- II = cd#0;
-- (A,c) = ((partialCharacter(II))#1 , (partialCharacter(II))#2)