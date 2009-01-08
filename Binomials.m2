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
Lsat = (A) -> syz transpose syz transpose A;

-- Ideal containment done "by hand".
contained = (I,J) -> (
     -- Returns true if I is contained in J
     jbase := gb J;
     ibase := flatten entries gens gb I;
     for g in ibase do (
	  if g % jbase != 0 then (
	       return false;
	       );
	  );
     return true;
     )
     

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
     cv := set cellVars I; 
     -- Here go the non-cell variables
     ncv := toList (set gens R - cv);
     -- We map I to the subring: k[ncv]
     CoeffR := coefficientRing R;
     S := CoeffR[ncv];
     J := kernel map (R/I,S);
          
     Q = S/J;
     slist = flatten entries flatten basis Q;
     use R;
     return slist;
     )

IdealfromCharacter = (R,A,c) -> (
     -- Constructs the Ideal I_+(c) in R
     -- R is a ring in which the ideal is returned
     -- The columns of A should contain exponent vectors of generators
     -- The vector c contains the corresponding coefficients which must lie
     -- in the coefficient ring of R !!!
     
     use R;
     if A == 0 then return ideal 0_R;
     
     -- We coerce the coefficients to R:
     c = apply (c, a -> (sub (a,R)));
      
     var := gens R;
     cols := entries transpose A;
     posmon := 1;
     negmon := 1;
     binomials := {};
     for i in 0..numcols A-1 do (
	  for j in 0..numrows A-1 do (
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
     -- print ideal (binomials);
     -- If the coefficients are all "1". Can we use 4ti2 here?
     -- TODO: This saturation will typically fail if 
     -- we have complex coefficients :(
     
     return saturate (ideal binomials, product var);
     )

-- How to do overloading ?	  
-- IdealfromCharacter = (R,A) -> (
--     c := {};
--     for i in (1..numcols A) do c = c | {1};
--     return IdealfromCharacter(R,A,c);
--     )

satpchar = (va, A, c) -> (
     -- This function saturates a partial character, 
     -- numerically if needed.
     
     -- Todo : Clean up the types. 
     -- Currently a saturated character is distinguished from its 
     -- saturation as the saturation has a list as third entry.
     
     -- If the lattice is saturated, the character is saturated     
     if (image Lsat A == image A) then (
	  return (va, A, {c});
	  );
     
     -- The saturated lattice
     S := Lsat(A);
     -- The coefficient matrix :
     K := A // S;
     
     -- print K;
     -- Now we find the (binomal) equations for the saturated character:
     numvars := numrows K;
     varlist := for i in (0..numvars-1) list value ("m"|i);
     Q := QQ[varlist / value];
     eqs := IdealfromCharacter(Q,K,c);
     
     -- print eqs;
     -- print ring eqs;
     
     -- We carefully(tm) clear denominators:
     eqs = saturate(eqs, product gens ring eqs);
     
     -- And solve using singsolve:
     result = singsolve (eqs);
     return (va, S, result);
     )

satIdeals = (va, A, d) -> (
     -- computes all the ideals belonging to saturations of 
     -- a given partial character.
     satpc = satpchar(va, A, d);
     Q := CC[satpc#0];
     satideals = apply (satpc#2 , (c) -> (
	       -- print {Q, satpc#1, c};
	       IdealfromCharacter(Q,satpc#1,c)));
     return satideals;
     )

testPrimary = (I) ->(
     -- Implements Alg. 9.4 in [ES96]
     -- I must be a cellular ideal
     -- Returns the radical of I and whether I is primary

     -- The ring of I :
     R := ring I;
          
     -- Get the partial character of I
     pc := partialCharacter(I);
     noncellvars := toList(set (gens R) - pc#0);
     M := sub (ideal (noncellvars),R);
     -- print M;
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     CoeffR := coefficientRing R;
     S := CoeffR[pc#0];
     -- The the radical missing the monomials:
     prerad := kernel map (R/I,S);
     -- print prerad;
     
     rad := sub (prerad ,R) + M;
     print "The radical is:";
     print rad;
     
     -- If the partial character is not saturated, 
     -- the radical is not prime
     if image Lsat(pc#1) != image pc#1 then (
	  print "The radical is not prime, as the character is not saturated";
	  -- We can output distinct associated primes by 
	  -- saturating the character here ...
	  );
     
     -- The list of maximally standard monomials:
     mono1 := monomialIdeal (I); -- Initial ideal of I
     mono1 = quotient (mono1, M); -- Quotient with respect to non-cell-variables
     mono2 := monomialIdeal (I); -- This will hold in(I) + (x_i : i \in cellvars)
     print mono2;
     for var in pc#0 do (
	  print var;
	  print monomialIdeal(var);
	  mono2 = mono2 + monomialIdeal(var);
	  );
     
     -- We want the list of monomials that are in mono1, but not mono2.
     -- We take bases of the quotient rings and subtract there:
     l2 := flatten entries basis (ring mono2 / mono2);
--     print l2;
     l1 := flatten entries basis (ring mono1 / mono1);
--     print l1;

     -- Before doing this, we have to map everything back 
     -- to the original ring to make the comparison work!
     l1 = l1 / ((p) -> sub (p,R));
     l2 = l2 / ((p) -> sub (p,R));
     maxstdmon := toList (set(l2) - set(l1));
     print "The maximally standard monomials are:";
     print maxstdmon;
     
     for m in maxstdmon do (
	  q := quotient (I, m);
	  -- Mapping down to cellvars:
	  q2 := kernel map (R/q,S);
     	  -- I_+(sigma) was called prerad above:
	  if not contained (q2, prerad) then (
	       print "not primary!";
	       -- We should output two associated primes here ...
	       );
	  );
     print "I is primary";
     return I;	  
     )

BinCellAssPrim = (I) -> (
     -- Computes the associated primes of cellular binomial ideal
     -- Warning: This function is untested !
     
     R := ring I;
     cv := cellVars(I); -- cell variables E
     -- print "Cellvars:"; print cv;
     primes := {}; -- This will hold the list of primes
     ncv := toList(set (gens R) - cv); -- non-cell variables x \notin E
     -- print "Noncellvars"; print ncv;
     ml := nonCellstdm(I); -- List of std monomials in ncv
     -- Coercing to R:
     ml = ml / ((m) -> sub (m,R) );
     -- print ml;
     -- The ring k[E]:
     CoeffR := coefficientRing R;
     S := CoeffR[cv];
     prerad := kernel map (R/I,S);
     -- The primes will live in a complex ring... 
     CR = CC[gens R];
     M := sub (ideal (ncv),CR); -- The monomial radical ideal
     -- A dummy ideal and partial Characters:
     Im := ideal;
     pC := {}; sat = {};
     for m in ml do (
	  print m;
	  Im = kernel map (R/(I:m),S);
	  pC = partialCharacter(Im);
	  sat = satIdeals(pC);
	  -- Coercing back to R:
	  sat = sat / ((I) -> sub (I,CR));
	  sat = sat / ((I) -> I + M);
	  primes = primes | sat;
	  );
     return primes;
     )   
     
-- cd = binomialCD(J)
-- II = cd#0;
-- pC = partialCharacter(II);
-- spC = satpchar(pC);
     
-----------------------------------
-- The island of misfit mascots  --
-- (and unneeded code parts)     --
-----------------------------------

-- satpchar = ( A , c) -> (
--      -- print A;
--      -- print c;
-- 
--      -- If the lattice is saturated, the character is saturated     
--      if (image Lsat A == image A) then (
-- 	  return (A,c);
-- 	  );
--      
--      S := Lsat(A);
--      K = A // S;
--      
--      sageprogfile := temporaryFileName() | ".sage";
--      sageoutfile := temporaryFileName();
--      -- We paste the whole program in:
--      F := openOut(sageprogfile);
--      
-- F << "S = matrix(ZZ,[";
-- -- Here goes the saturated lattice defining matrix
-- ent := entries S;
-- for r in (0..(#ent -1)) do (
--      F << "[";
--      for c in (0..(#(ent#r)-1)) do (
-- 	  F << ent#r#c;
-- 	  if (c < (numcols S) -1 ) then F << ",";
-- 	  );
--      F << "]";
--      if (r < (numrows S) -1) then F << ",";
--      );
-- F << "])" << endl;
--      
-- F << "A = matrix(ZZ,[";
-- -- Here goes the lattice defining matrix
-- ent = entries A;
-- for r in (0..(#ent -1)) do (
--      F << "[";
--      for c in (0..(#(ent#r)-1)) do (
-- 	  F << ent#r#c;
-- 	  if (c < (numcols A) -1 ) then F << ",";
-- 	  );
--      F << "]";
--      if (r < (numrows A) -1) then F << ",";
--      );
-- F << "])" << endl;
-- 
-- F << "K = matrix(ZZ,[";
-- -- Here goes the coefficient matrix
-- ent = entries K;
-- for r in (0..(#ent -1)) do (
--      F << "[";
--      for c in (0..(#(ent#r)-1)) do (
-- 	  F << ent#r#c;
-- 	  if (c < (numcols K) -1 ) then F << ",";
-- 	  );
--      F << "]";
--      if (r < (numrows K) -1) then F << ",";
--      );
-- F << "])" << endl;
-- 
-- -- Here goes the character
-- F << "l = [";
-- for i in (0..((#c)-1)) do (
--      F << c#i ;
--      if (i< (#c -1)) then F << ",";
--      );
-- F << "]" << endl;
-- 
-- -- The main program
-- F << "varnames = []" << endl;
-- F << "rg = len(S.columns())" << endl;
-- F << "for i in range(rg) :" << endl;
-- F << "    varnames = varnames + ['m'+str(i)]" << endl;
-- F << "for v in varnames:" << endl;
-- F << "    # print v" << endl;
-- F << "    var (v)" << endl;
-- F << "eqns = []" << endl;
-- F << "kr = len(K.rows())" << endl;
-- F << "kc = len(K.columns());" << endl;
-- F << "for col in range(kc):" << endl;
-- F << "    monom = 1" << endl;
-- F << "    for row in range(kr):" << endl;
-- F << "        monom *= eval('m'+str(row))^K[row,col]" << endl;
-- F << "        # print eval('m'+str(row))^K[row,col]" << endl;
-- F << "    eqns = eqns + [ monom - l[col] ]" << endl;
-- F << "satlist = [] # The list of saturations" << endl;
-- F << "vs = [eval(v) for v in varnames]" << endl;
-- F << "if (len (eqns) > 1) :" << endl;
-- F << "    s = solve (eqns , tuple(vs), solution_dict=True)" << endl;
-- F << "else :" << endl;
-- F << "    spre = solve (eqns , tuple(vs))" << endl;
-- F << "    # print spre" << endl;
-- F << "    s= [dict([(eq.left(),eq.right())]) for eq in spre ]" << endl;
-- F << "m = [] " << endl;
-- F << "for sol in s :" << endl;
-- F << "    n = [] " << endl;
-- F << "    for v in varnames:" << endl;
-- F << "        n = n + [sol[v]]" << endl;
-- F << "    m = m + [n]" << endl;
-- 
-- -- Here we do output
-- F << "charstr = str(m).replace('I','ii');" << endl;
-- F << "charstr = charstr.replace('[','{');" << endl;
-- F << "charstr = charstr.replace(']','}');" << endl;
-- F << "print 'c := ' + charstr" << endl;
-- 
--      close (F);
--      
--      execstr = "sage "|sageprogfile | " > " | sageoutfile ;
--      -- print execstr;
--      ret := run (execstr);
--      if (ret != 0) then (
-- 	  print "sage did not run correctly, sorry :(";
-- 	  return False;
-- 	  );
--      
--      outlines := lines get sageoutfile;
--      
--      cl := value outlines#0;
--      return (S,cl)
--      )

