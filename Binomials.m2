
-- -*- coding: utf-8 -*-
--  Binomials.m2
--
--  Copyright (C) 2009 Thomas Kahle <kahle@mis.mpg.de>
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or (at
--  your option) any later version.
--
--  This program is distributed in the hope that it will be useful, but
--  WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  General Public License for more details.
--
--  You should have received a copy of the GNU General Public License along
--  with this program; if not, write to the Free Software Foundation, Inc.,
--  59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newPackage(
	"Binomials",
    	Version => "0.3", 
    	Date => "May 2009",
    	Authors => {
	     {Name => "Thomas Kahle", Email => "kahle@mis.mpg.de", HomePage => "http://personal-homepages.mis.mpg.de/kahle/"}},
    	Headline => "Spezialised routines for binomial Ideals",
	Configuration => { },
    	DebuggingMode => true
    	)
   
export {binomialCD,
     partialCharacter,
     testCellular,
     cellVars,
     Lsat,
     idealFromCharacter,
     LatticeBasisIdeal,
     saturatePChar,
     BinSolveWrap,
     satIdeals,
     testPrimary,
     BinomialMinimalPrimes,
     BinomialAssociatedPrimes,
     CellularBinomialAssociatedPrimes,
     CellularAssociatedLattices,
     CellularBinomialPrimaryDecomposition,
     BPD,
     testPrime,
     testRadical,
     BinomialRadical,
     CellularBinomialRadical,
     makeBinomial,
     doExample,
     nonCellstdm,
     maxNonCellstdm,
     BCDisPrimary,
     isBinomial,
     minimalPrimaryComponent,
     binomialQuasiPower,
     BinomialQuotient,
     projectToSubRing,
     removeRedundant,
--     lcm,
     -- Options
     cellVariables, -- for partialCharacter
     returnPrimes, -- for testPrimary 
     returnPChars, -- for testPrimary
     returnCellVars -- for binomialCD
     }

needsPackage "FourTiTwo";
needsPackage "PDBISolve";
needsPackage "cyclotomic"

axisSaturate = (I,i) -> (
-- By Ignacio Ojeda and Mike Stillman
-- For computing saturations w.r.t. a single variable:
-- Comments by TK:
    R := ring I;
    I1 := ideal(1_R);
    s := 0;
    f := R_i;
    while not(I1 == I) do (
	s = s + 1;
	I1 = I;
	-- This should be just the quotient. Is this faster ??
	I = ideal syz gb(matrix{{f}}|gens I,
            SyzygyRows=>1,Syzygies=>true););
    {s-1, I}
    )

-- Cellular decomposition of binomial ideals:
--

binomialCD = method (Options => {returnCellVars => false})
binomialCD Ideal := Ideal => o -> I -> (
-- By Ignacio Ojeda and Mike Stillman     
-- Comments by TK
     R := ring I;
     n := numgens R;
     Answer := {};
     L := null;
     IntersectAnswer := ideal(1_R);
     ToDo := {{{1_R},toList(0..n-1),I}};
     -- Each entry of the ToDoList is a triple:
     -- #0 contains list of variables with respect to which is already saturated
     -- #1 contains variables to be considered for cell variables
     -- #2 is the ideal to decompose
     compo := 0;
     next := () -> (
	 if #ToDo === 0 then false
	 else (
	      L = ToDo#0;
	      ToDo = drop(ToDo,1);
	      if gens IntersectAnswer % L#2 == 0
	      -- This reduces the result so far modulo the ideal under consideration
	      then (<< "redundant component" << endl;)
	      -- if its not redundant:
	      else if #(L#1) === 0 then ( -- #(L#1) counts 'remaining variables to check'
		   -- no variables remain to check :
		   -- We have an answer
                   compo = compo + 1; 
		   newone := trim L#2;
		   << "component: " << {compo, gens newone} << endl;
		   if o#returnCellVars then Answer = append(Answer,{newone, delete(1_R,L#0)})
		   else Answer = append (Answer,newone);
		   IntersectAnswer = intersect(IntersectAnswer,newone);
		   -- if we have enough, stop after this iteration
		   if IntersectAnswer == I then ToDo = {})
	      else ( -- So, there are remaining variables #(L#1) is not zero
	           i := L#1#0; -- i is a variable under consideration
		   newL1 = drop(L#1,1); -- gets removed from the list
	           result = axisSaturate(L#2, i); -- compute saturation wrt i
		   J := result#1; -- Ideal
		   k := result#0; -- Saturation Exponent
		   if k > 0 then ( -- If a division was needed:
     	       	    	-- We add the monomial i^k to ideal under consideration		      	   	
			J2 = L#2 + ideal(R_i^k); 
     	       	    	-- And remove L#0 components from variables that we already
			-- considered before
			J2 = saturate(J2, product L#0);
			if J2 != ideal(1_R) then
			    -- If something is left after removing we have more to decompose J2
			    ToDo = prepend({L#0, newL1, J2},ToDo));
		       -- Continue with the next variable and add i to L#0
		   if J != ideal(1_R) then ToDo = prepend({L#0|{R_i}, newL1, J},ToDo);
		   );
	      true));
     while next() do ();
     Answer	      
     )

-- This function saturates an integer lattice. It expects 
-- the matrix A, whose image is the lattice. 
Lsat = A -> syz transpose syz transpose A;

testCellular = method (Options => {returnCellVars => false})
testCellular Ideal := Ideal => o -> I -> (
     R := ring I;
     cv := cellVars I;
     if cv == {} then prod := 1_R else prod = product cv;
     if I == saturate (I, prod) then (
	  -- Cellular Ideal
	  if o#returnCellVars then return cv
	  else return true;
	  )
     else return false;
     )

partialCharacter = method (Options => {cellVariables => null})
partialCharacter Ideal := Ideal => o -> I -> (
     -- Will compute the partial character associated to a cellular binomial Ideal.
     -- If the cell variables are known they can be given as an optional argument,
     -- to save cpu cycles.
     vs := {}; -- This will hold the lattice generators
     vsmat := matrix "0"; -- Holds the matrix whose image is L 
     cl := {}; -- This will hold the coefficients
     R := ring I;
     CoeffR := coefficientRing R; -- needed to form terms below
     scan (gens R, (v -> v = local v));
     II := ideal;
     
     -- print o.cellVariables;
     -- The input should be a cellular ideal 
     cv := null; -- Getting a local name
     if o#cellVariables === null then (
	  -- No cell variables are given -> compute them
	  cv = cellVars I;
	  )
     else cv = o#cellVariables;
     
     -- The cell ring:
     S := CoeffR[cv];
         
     -- If there are no cellular variables, 
     -- the ideal is monomial and the partial character is zero:
     if cv == {} then (
	  return ({}, matrix "0", {1});
	  );

     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     if #cv != #(gens R) then (
     	  II = kernel map (R/I,S);
	  )
     else (
	  II = I;
	  );

     -- The partial Character of the zero ideal is the 
     -- zero lattice.       
     if ( II == 0 ) then (
	  for i in cv do vs = vs | { 0_ZZ };
	  cl = {1_ZZ};
	  return (cv, transpose matrix {vs}, cl);
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
	  vs = vs | {((exponents t)#0 - (exponents t)#1)};
	  -- print vs;
	  vsmat = transpose matrix vs;
	  
	  -- Do we need the new generator ?
	  if image oldmat == image vsmat then (
	       -- Undo changes:
	       vsmat = oldmat;
	       vs = oldvs;
	       )
	  else (
	       -- So we have a new generator : update coefficient list
	       coeffs := entries ((coefficients(t))#1);
               cl = cl | { sub (-coeffs#1#0 / coeffs#0#0, CoeffR) }
	       );
	  );
--    print coeffs;
--    print cl;
     
     -- back to the old ring
     -- is this needed ?
     use R;
     return (cv, transpose matrix vs , cl);
     )

isBinomial = I -> (
     ge := flatten entries gens I;
     for g in ge do (
          if #(terms g) > 2 then return false;	  
	  );
     return true;
     )
     
cellVars = I -> (
     print "Warning, cellVars called, could be unessary";
     cv := {};
     for i in gens ring I do if saturate (I,i) != substitute(ideal(1), ring I) then cv=cv|{i};
     return cv;
     )

nonCellstdm = {cellVariables=>null} >> o -> I -> (
     cv2 := {};
     if o#cellVariables === null then (
	  print "CellVariables not given, Please consider precomputing them";
	  cv2 = cellVars I;
	  )
     else cv2 = o#cellVariables;
     -- Extracts the monomials in the non-Cell variables.
     R := ring I;
     scan (gens R, (v -> v = local v));     
     cv := set cv2; 
     -- Here go the non-cell variables
     ncv := toList (set gens R - cv);
     -- We map I to the subring: k[ncv]
     CoeffR := coefficientRing R;
     S := CoeffR[ncv];
     J := kernel map (R/I,S); -- image of I in the subring S
     Q = S/J; 
     slist = flatten entries flatten basis Q;
     use R;
     return slist;
     )

maxNonCellstdm = {cellVariables=>null} >> o -> I -> (
     -- Extracts the maximal elements in the set of monomials 
     cv := {};
     if o#cellVariables === null then (
	  print "CellVariables not given, Please consider precomputing them";
	  cv = cellVars I;
	  )
     else cv = o#cellVariables;

     nm := nonCellstdm (I,cellVariables=>cv);
     -- print nm;
     result := {};
     maxel := 0;
     while nm != {} do (
     	  maxel = max nm;
     
          -- Add maxel to the result
      	  result = result | {maxel};

          -- Delete everyone who is dividing maxel     
     	  nm = for m in nm list (if maxel // m != 0 then continue; m);
     );

     return result;
     )

makeBinomial = (R,m,c) -> (
     -- constructs the binomial associated to 
     -- exponent vector m and coefficient c in R
     var := gens R;
     posmon :=1;
     negmon :=1;
     for i in 0..#m-1 do (
     	  if m#i > 0 then (
		    posmon = posmon * var#i^(m#i)
		    )
	       else (
		    negmon = negmon * var#i^(-m#i)
		    );
	       );	  
     return posmon - c*negmon;
     )

idealFromCharacter = (R,A,c) -> (
     -- Constructs the Ideal I_+(c) in R
     -- R is a ring in which the ideal is returned
     -- The columns of A should contain exponent vectors of generators
     -- The vector c contains the corresponding coefficients which must lie
     -- in the coefficient ring of R !!!
     
     use R;
     var := gens R;
     if A == 0 then return ideal 0_R;
     cols := null;
     binomials :=null;
     
     idmat := matrix mutableIdentity(ZZ,#var);
     if A == idmat then (
	  -- If A is the unit matrix we are lucky,
	  -- no saturation is needed.

	  -- We coerce the coefficients to R:
	  c = apply (c, a -> (sub (a,R)));
     	  cols = entries transpose A;    
     	  binomials = for i in 0..numcols A-1 list makeBinomial (R,cols#i, c#i);	  
	  return ideal binomials
	  )
     else if set c === set {1} then (
	  -- all coefficients are one, we can use 4ti2.
	  return toricMarkov (transpose A, R, InputType => "lattice");
	  )
     else (
     	  -- The general case, fall back to saturation in M2:
	  c = apply (c, a -> (sub (a,R)));
     	  cols = entries transpose A;    
	--  for i in 0..numcols A-1 do print (R,cols#i,c#i);
     	  binomials = for i in 0..numcols A-1 list makeBinomial (R,cols#i, c#i);
     	  return saturate (ideal binomials, product var);
	  );
     )

LatticeBasisIdeal = (R,L) -> (
     -- Constructs the lattice basis ideal (whose saturation is the toric ideal)
     -- Convention is that L's columns generate the lattice.
     use R;
     var := gens R;
     if L == 0 then return ideal 0_R;
     cols := null;
     binomials :=null;
     cols = entries transpose L;
     binomials = for i in 0..numcols L-1 list makeBinomial (R,cols#i, 1);
     return ideal binomials;
     )

saturatePChar = (va, A, c) -> (
     -- This function saturates a partial character.
     
     -- Currently a saturated character is distinguished from its 
     -- saturation as the saturation has a list as third entry.
     
     -- If the lattice is saturated, the character is saturated     
     if image Lsat A == image A then (
	  return (va, A, {c});
	  );
     
     -- The saturated lattice
     S := Lsat(A);
     -- The coefficient matrix :
     K := A // S;
     
     -- print K;
     -- Now we find the (binomal) equations for the saturated character:
     numvars := numrows K;
     varlist := for i in 0..numvars-1 list value ("m"|i);
     scan (varlist, (v -> v = local v));
     Q := QQ[varlist];
     eqs := idealFromCharacter(Q,K,c);
     
     -- print "The character defining equations are:";
     -- print eqs;
     -- print ring eqs;
     
     result = BinomialSolve (eqs,ww);
--     print "In saturatePChar the result is";
--     print result;
     return (va, S, result);
     )

BinSolveWrap = I ->(
     -- Should find the solutions to the pure binomial system 
     -- and construct a cyclotomic field in which all exist.
     -- Currently it will set to zero everything that is not 
     -- in QQ.
     sols = BinomialSolve I;
     for sol in sols do(
	  for entry in sol do(
	       entry = sub (entry, QQ);
	       );
	  );
     return sols;
     )
     

satIdeals = (va, A, d) -> (
     -- Computes all the ideals belonging to saturations of 
     -- a given partial character.
     -- TODO: Construct the correct coefficient field
     satpc := saturatePChar(va, A, d);
--     print "The cyclotomic field is:";
--     print ring satpc#2#0#0; -- The apropriate cyclotomic field
     scan (satpc#0, (v -> v = local v));     
     -- The following should be the smallest ring 
     -- containing all new coefficients
     F := ring satpc#2#0#0;
     Q := F[satpc#0];
     satideals = apply (satpc#2 , (c) -> (
	       -- print {Q, satpc#1, c};
	       idealFromCharacter(Q,satpc#1,c)));
     return satideals;
     )

BinomialRadical = I -> (
     	  cv := testCellular (I, returnCellVars=>true);
     	  if not cv === false then (
	       return CellularBinomialRadical (I,cellVariables=>cv)
	       )
      	  else (
	  -- In the general case
	  print "Input not cellular, computing minimial primes ...";
	  mp := BinomialMinimalPrimes I;
	  print mp;
	  return ideal mingens intersect mp;
	  )

     )

CellularBinomialRadical = method (Options => {cellVariables => null})
CellularBinomialRadical Ideal := Ideal => o -> I -> (
     
     cv := {};
     if o#cellVariables === null then (
	  print "CellVariables not given, Please consider precomputing them";
	  cv = cellVars I;
	  )
     else cv = o#cellVariables;
     
     -- Computes the radical of a cellular binomial ideal
     R := ring I;
     scan (gens R, (v -> v = local v));
     -- Get the partial character of I
     pc := partialCharacter(I, cellVariables=>cv);
     noncellvars := toList(set (gens R) - pc#0);
     	       
     M := sub (ideal (noncellvars),R);
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     -- The the radical missing the monomials:
     prerad := projectToSubRing (I,pc#0);
     return prerad + M;
     )

testPrimary = method (Options => {returnPrimes => false , returnPChars => false, cellVariables=> null})
testPrimary Ideal := Ideal => o -> I -> (
     -- Implements Alg. 9.4 in [ES96]
     -- I must be a cellular ideal, cellVariables can be given for speedup
     -- Returns the radical of I and whether I is primary
     -- if the option returnPrimes is true, then it will return 
     -- the radical in the affirmative case and two distinct associated primes
     -- otherwise
     -- if the option returnPChars is true then it will return partial Characters 
     -- of the primes instead. 
     -- If both are true then it will return characters.
     
     cv := {};
     if o#cellVariables === null then (
	  print "CellVariables not given, Please consider precomputing them";
	  cv = cellVars I;
	  )
     else cv = o#cellVariables;
     -- The ring of I :
     R := ring I;
     scan (gens R, (v -> v = local v));
     
     -- Only proper ideals are considered primary
     if I == ideal(1_R) then return false;      
     
     -- Get the partial character of I
     pc := partialCharacter(I, cellVariables=>cv);
     noncellvars := toList(set (gens R) - cv);
     
     M := sub (ideal (noncellvars),R);
     -- print ("The monomial ideal M: " | toString M);
     
     -- We intersect I with the ring k[E]
     -- The the radical missing the monomials:
     prerad := projectToSubRing (I,cv);
     
     rad := prerad + M;
     
     -- If the partial character is not saturated, the radical is not prime
     if image Lsat pc#1 != image pc#1 then (
	  print "The radical is not prime, as the character is not saturated";
	  satpc := saturatePChar pc;
	  if o#returnPChars then (
	       -- This one is the fastest, so check it first
	       return {{satpc#0,satpc#1,satpc#2#0}, {satpc#0,satpc#1,satpc#2#1}}
	       );
	  if o#returnPrimes then (
	       ap1 := sub (idealFromCharacter (S,satpc#1,satpc#2#0), R) + M;
	       ap2 := sub (idealFromCharacter (S,satpc#1,satpc#2#1), R) + M;
	       -- Return two distinct associated primes:
	       return {ap1,ap2};
     	       )	   	       
	  else return false;
	  );
     
     -- If the radical is prime, then there still might be embedded
     -- primes that properly contain the radical. The remaining part
     -- finds such primes by examining quotients w.r.t (maximal)
     -- standard monomials. 
     
     -- The list of maximally standard monomials:
     maxstdmon := maxNonCellstdm (I,cellVariables=>cv) / (i -> sub (i,R));
     -- print "The maximally standard monomials are:";
     -- print maxstdmon;
     
     for m in maxstdmon do (
	  q := quotient (I, m);
	  -- Mapping down to cellvars:
	  q2 := projectToSubRing (q,cv);
     	  -- I_+(sigma) was called prerad above:
	  if not isSubset(q2, prerad) then (
	       -- creating some local names:
	       qchar := partialCharacter (q,cellVariables=>cv);
	       satqchar := saturatePChar qchar;
	       if o#returnPChars then(
		    return {pc, {satqchar#0,satqchar#1,satqchar#2#0}}
		    );
	       if o#returnPrimes then (
		    ap2 := idealFromCharacter (S,satqchar#1,satqchar#2#0);
		    return {rad, sub(ap2,R) + M};
     	       	    )  
	       else return false;
	       );
	  );
     -- print "Ideal is primary";
     if o#returnPChars then return {pc};
     if o#returnPrimes then return {rad};
     return true;	  
     )

testPrime = I -> (
     -- A binomial ideal is prime if all its 
     -- monomial generators have power one and the 
     -- associated partial character is saturated.
     -- (Corollary 2.6 in ES96 )
     
     R := ring I;
     if I == ideal (1_R) then return false;
     pc := partialCharacter I;
     ncv := toList(set (gens R) - pc#0);
     for v in ncv do (
	  if not isSubset(ideal (v) , I) then return false;
     	  );

     -- Is the partial character saturated ???     
     if image Lsat pc#1 != image pc#1 then return false;
     
     -- all tests passed:
     return true;
     )

BinomialMinimalPrimes = I -> (
     -- Computes the minimial Primes with Algorithm 9.2 in ES96
     -- TODO: This function typically fails due to large demand for memory
     -- TODO: Implement the shortcut mentioned below the Algorithm
     
     R := ring I;
     -- Compute all subsets of variables
     everything := ideal (1_R);
     g := set gens R;
     ss := subsets g; 
     mp := {}; -- will hold the minimial primes
     Is := null; -- Will hold candidate ideals
     ME := null;
     for s in ss do (
	  ME = sub (ideal toList (g - s) , R); -- The monomial ideal outside s
	  Is = saturate ( I + ME, sub (ideal product toList s, R));
	  if Is == everything then continue
	  else (
	       pc = partialCharacter Is;
	       si := satIdeals pc;
	       si = apply (si , i -> sub(i,R)); -- Coercing to R;
	       si = si / (i -> (i + ME)); -- Adding monomials;
	       mp = mp | si;
	       );
	  );
     -- print mp;
     return removeEmbedded mp;
     )

removeEmbedded = l -> (
     -- Computes the minimal primes from a list of primes.  
     
     -- Algorithm: Copy the input list, then walk through the input
     -- list and remove from the copy every element which contains the
     -- element at hand.
     
     ToDo := copy l;
     i := ideal;
     su := {};
     while #ToDo > 0 do (
--	  print ToDo;
--	  print l;
	  i = ToDo#0;
	  su = for i2 in l list (if (isSubset (i,i2)) and (i!=i2) then i2);
	  
     	  -- Remove any occurrences of redundant primes from l 
	  -- and the todolist;
	  for s in su do (
	       ToDo = delete (s, ToDo);
	       l = delete (s, l);
	       );
	  -- Remove i from the todolist;
	  ToDo = delete (i, ToDo);
	  );
     return l;
     )
      
CellularBinomialAssociatedPrimes = method (Options => {cellVariables => null})
CellularBinomialAssociatedPrimes Ideal := Ideal => o -> I -> ( 
     -- Computes the associated primes of cellular binomial ideal
     
     -- TODO: It could be faster by rearringing things in the m in ml
     
     R := ring I;
     scan (gens R, (v -> v = local v));
     
     cv := null;
     if o#cellVariables === null then (
	  -- No cell variables are given -> compute them
	  cv = cellVars(I);
	  )
     else cv = o#cellVariables;
     
     primes := {}; -- This will hold the list of primes
     ncv := toList(set (gens R) - cv); -- non-cell variables x \notin E
     ml := nonCellstdm(I,cellVariables=>cv); -- List of std monomials in ncv
     -- Coercing to R:
     ml = ml / ( m -> sub (m,R) );
     -- Mapping to the ring k[E]:
     prerad := projectToSubRing (I,cv);
     M := sub (ideal (ncv),R); 
     -- The monomial radical ideal 
     
     -- Here is a nice shortcut: if prerad is zero, we are done since
     -- all I:m will be zero after intesection with the cell ring, right?
     if prerad == ideal (0_R) then return {M};
     -- A dummy ideal and partial Characters:
     Im := ideal;
     pC := {}; sat = {};
     for m in ml do (
	  -- print m;
	  Im = projectToSubRing (I:m,cv);
	  -- Do we already know the cell variables in the following computation?
	  pC = partialCharacter(Im , cellVariables=>cv);
	  if pC#1 == 0 then (
	       primes = primes | {ideal(0_R)}; 
	       continue;
	       );
	  sat = satIdeals(pC);
	  primes = primes | sat;
	  );
     -- We need to remove redundant elements
     -- We coerce all associated primes to an apropriate
     -- new ring that contains all their coefficients
        
     l := lcm for p in primes list FindRootPower (ring p);
     v := gens R;
     S := Ring;
     -- Down here we reuse the Symbol S...
     if l<3 then(
	  -- Coefficients are in QQ !
	  -- Assumed to be the original ring
	  S = R;
	  )
     else (
	  -- Construct a new cylcotomic field which contains all
	  -- necessary coefficients
	  F := cyclotomicField(l,QQ[ww]);
	  S = F[v];
	  );
     primes = primes / ( I -> sub (I,S));
     M = sub (ideal (ncv), S);
     primes = primes / (I -> I + M);

     use R;
     return toList set primes;
     )

BinomialAssociatedPrimes = I -> (
     -- Todo: Compute the Associated Primes of any Binomial Ideal
     if testCellular I then return CellularBinomialAssociatedPrimes I 
     else error "Not implemented, sorry!";
     )

CellularAssociatedLattices = I -> (
     -- Computes the associated lattices of a cellular binomial ideal
     -- Todo: Can we get the multiplicities too ?
     
     R := ring I;
     scan (gens R, (v -> v = local v));
     cv := cellVars I; -- cell variables E
     lats := {}; -- This will hold the list of lattices
     ncv := toList(set (gens R) - cv); -- non-cell variables x \notin E
     -- print "Noncellvars"; print ncv;
     ml := nonCellstdm(I,cellVariables=>cv); -- List of std monomials in ncv
     -- Coercing to R:
     ml = ml / ( m -> sub (m,R) );
     -- The ring k[E]:
     prerad := projectToSubRing (I,cv);
     -- A dummy ideal and partial Characters:
     Im := ideal;
     pc := {};
     redundant := true;
     -- For each monomial, check if I:m has a different lattice !
     for m in ml do (
	  -- print m;
	  Im = projectToSubring ((I:m),cv);
	  -- We already know the cell variables in the following computation
	  pc = partialCharacter(Im, cellVariables=>cv);
	  if #lats == 0 then (
	       lats = {pc#1};
	       continue;
	       )
	  else (
	       redundant = false;
	       scan (lats, (l -> (if image l == image pc#1 then redundant = true)))
     	       );
	  if redundant then continue
	  else (
	       lats = lats | {pc#1};
	       );
      	  ); -- for m in ml	    
     return {cv, lats};
     ) -- CellularAssociatedLattices

BCDisPrimary = I -> (
     print "Computing Cellular Decomposition";
     cd := binomialCD I;
     print "Testing for primaryness of components";
     i := 0;
     for c in cd do (
	  i = i+1;
	  print ("Component number " | i );
	  if testPrimary c == true then continue;
	  print "Following component is not primary: ";
	  print c;
	  return false;
	  );
     print "The cellular decomposition is primary !";
     return cd;
     )

minimalPrimaryComponent = method (Options => {cellVariables => null})
minimalPrimaryComponent Ideal := Ideal => o -> I -> (
     -- Input a cellular binomial ideal whose radical is prime.
     -- Ouptut, generators for Hull(I)

     cv := null;
     if o#cellVariables === null then (
	  -- No cell variables are given -> compute them
	  cv = cellVars(I);
	  )
     else cv = o#cellVariables;

     apc := testPrimary (I, returnPChars=>true, cellVariables => cv);
     if #apc == 1 then return I -- radical is only associated prime!
     else (
	  R := ring I;
	  -- A trick to not clobber the global variables
	  scan (gens R, (v -> v = local v));
	  
     	  pc1 := apc#0;
	  pc2 := apc#1;
	 
	  -- ap#0 and ap#1 correspond to 
	  -- distinct lattices L1 and L2
	  L1 := image pc1#1;
	  L2 := image pc2#1;

	  L := intersect {L1,L2};
	  -- The index of L inside L2 is finite if and only if their dimensions coincide
	  if rank L == rank L2 then (
	       print "finite index case !";
	       -- The finite index case :  
	       
	       -- Compute a binomial in J2 which is not in J1.
	       -- i.e. find a generator on which pc1 and pc2 take different values.
	       print pc1;
	       print pc2;
	       for i in 0..#(pc2#2)-1 do (
	       	    if pc1#2#i == pc2#2#i then continue
	       	    else (
		    	 -- Character differs. Form binomial:
		    	 b := makeBinomial (QQ[pc2#0], (entries transpose pc2#1)#i, pc2#2#i );
		    	 print b;
		    	 break;
		    	 );
	       	    );
	       -- Take the quotient of I with respect to b, such that the result is binomial
	       return minimalPrimaryComponent (BinomialQuotient (I,b, cellVariables=>cv), cellVariables=>cv);
	       )
       	   else (
		-- print "infinite index case !";
		-- The case of infinite index :
		    
                -- Find an exponent vector which has infinite order:
		-- i.e. a vector m \in L2 such that image m \cap L has dimension < 1;
		-- One of the generators must have this property !
     		    
		 -- Here are the lattice generators
		 L2cols := entries transpose pc2#1;
		 -- print L2cols;
		 -- Try them one by one:
		 i := 0; -- Counter to determine which generator fits
		 for c in L2cols do (
		      -- The span of c:
		      imc := image transpose matrix {c};
		      if rank intersect {imc , L} < 1 then (
			   -- We have winner 
			   m := c;
			   break;
			   );
		      -- Lets try the next vector.
		      i = i+1;
		      );
		 -- print i;
     	         -- now i has the suitable index !
		 b = makeBinomial(QQ[pc2#0], L2cols#i, pc2#2#i);		    
		 -- print b;
	    	 -- Take the quotient of I with respect to b, such that the result is binomial
	    	 return minimalPrimaryComponent (BinomialQuotient (I,b, cellVariables=>cv), cellVariables=>cv);
	    	 );
	    ) -- else path of if not testPrimary
     ) -- minimalPrimaryComponent

BinomialQuotient = {cellVariables => null} >> o -> (I,b) -> (
     -- Algorithm A.3 in Ojeda / Sanchez
     -- Input I - Cellular Binomial Ideal 
     -- b -- Binomial in the cell variables of I which is a zerodivisor mod I
     -- Output : The quotient (I : b^[e]) for a suitably choosen e, such that the
     -- result is binomial
     
     R := ring I;
     scan (gens R, (v -> v = local v));
     
     cv := null;
     if o#cellVariables === null then (
	  -- No cell variables are given -> compute them
	  cv = cellVars(I);
	  )
     else cv = o#cellVariables;
     
     --First check if we can save a lot of time if already I:b is binomial,
     -- and no quasipowers have to be taken.
     quot :=  quotient (I , sub(ideal(b),R));
     if isBinomial quot then return quot;
          
     --Transporting the standardmonomials to R:
     ncvm := (i -> sub (i,R) ) \ nonCellstdm (I,cellVariables=>cv) ;
     -- print ncvm;
  
     U' := {}; -- U' as in the paper
     D  := {};
     J := ideal (0_R); -- initialize with zero ideal
     bexp := (exponents b)#0 - (exponents b)#1; -- exponent vector of b
     -- We will often need the image of bexp, so lets cache it
     bexpim := image transpose matrix {bexp};
     pc := {}; -- Will hold partial characters;
     -- CoeffR := coefficientRing R;
     -- S := CoeffR[cv]; -- k[\delta] in the paper
     
     for m in ncvm do(
	  quot = I:m;
	  	  
	  -- Mapping to k[delta] and taking character
	  quot = projectToSubRing (quot, cv);
	  pc = partialCharacter (quot, cellVariables=>cv);
	  
	  --determine whether the exponents of b are in the saturated lattice
	  if isSubset (bexpim, image Lsat pc#1) then (
     	       U' = U' | {m};
	       i := 1;
	       -- Computing the order of bexp in Lsat / L
	       while true do (
		    if isSubset (image transpose matrix {i * bexp} , image pc#1) then (
			 D = D | {i};
			 break;
			 )
		    else i = i+1;
		    );
	       print ("The order of " | toString bexp | "in " | toString image pc#1 | "is " | toString i);
	       -- print D;
	       );
	  ); -- loop over monomials
     -- Compute the least common multiple of the orders
     e := lcm D; -- e' in paper, but we dont need e later.
     print ("binomialQuasiPower" | toString (b,e));
     bqp := sub (binomialQuasiPower (b,e) , R); -- e'th quasipower
     print bqp;
     print ring bqp;
     print ( "Least common multiple : " | toString e);
     for m in U' do(
	  quot = quotient (I,m);
	  if bqp % quot == 0 then J = J + ideal(m);		
     	  );
     print J;
     return I + J;
     )     

--lcm = l -> (
--     if #l == 0 then return 1;
--     sublcm := lcm delete (l#0,l);
--     return l#0 * sublcm / gcd (l#0, sublcm);
--     )

binomialQuasiPower = (b,e) -> (
     -- returns the e-th quasipower of the binomial b
     -- i.e. (b_1)^e - (b_2)^e
     return ((terms b)#0)^e - (- (terms b)#1)^e;
     )

BPD = I -> (
     -- The full binomial primary decomposition 
     -- starting from a not necessarily cellular binomial ideal
     cd := binomialCD (I, returnCellVars => true);
     counter := 1;
     cdc := #cd;
     bpd := {};
     scan (cd , ( (i) -> (
	   	    print ("Decomposing cellular component: " | toString counter | " of " | toString cdc);
		    counter = counter +1;
--		    print i;
--		    print CellularBinomialPrimaryDecomposition i;
		    bpd = bpd | CellularBinomialPrimaryDecomposition (i#0, cellVariables => i#1);
		    )
	       )
    	  ); -- apply
     -- print bpd;
     print "Removing redundant components (fast)";
     use ring I;
     return removeRedundant bpd;
     )

CellularBinomialPrimaryDecomposition = method (Options => {cellVariables => null})
CellularBinomialPrimaryDecomposition Ideal := Ideal => o -> I -> ( 
     -- computes the binomial primary decomposition of a cellular ideal
     -- I needs to be cellular. Cell variables can be given to speed up
     -- Implements algorithm 9.7 in ES96, respectively A5 in OS97
     ap := {};
     cv := null;
     if o#cellVariables === null then cv = cellVars I
     else cv = o#cellVariables;
     ap = CellularBinomialAssociatedPrimes (I, cellVariables => cv);
     -- Projecting down the assoc. primes, removing monomials
     proj := (I) -> projectToSubRing (I,cv); 
     pap := ap / proj ;
     R := ring ap#0; -- All associated primes live in a common ring
     J := sub (I,R); -- get I over there to compute sums
     -- Compute and return minimal primary Components. We can reuse
     -- the cell Variables here by a Proposition in the writeup
     return pap / ( (P) -> minimalPrimaryComponent (J + P, cellVariables=>cv));
     )

removeRedundant = l -> (
     -- Removes redundant components from a list of ideals to be intersected
     -- TODO: The ideals given might live in different rings, which are 
     -- mathematically the same. We should handle this in a nice way.
     if #l == 0 then error "empty list given !";
     Answer := l#0; -- Will hold Intersection of everything in the end
     result := {l#0};
     l = drop (l,1); -- Drop l#0;
     isect := ideal; -- dummy 
     while #l > 0 do (
	  isect = intersect (Answer , l#0); -- intersect with next
	  -- if something was happened, add l#0 to the result
	  if isect != Answer then (
	       result = result | {l#0};
	       Answer = isect;
	       print l#0;
	       )
	  else print "redundant component found !";
	  -- shorten the todolist
	  l = drop (l,1);
	  );
     return ideal \ mingens \ result;
     )

projectToSubRing = (I , delta) -> (
     -- projects an ideal down to the ring k[\delta] where delta is a
     -- the set of variables. Return after substituting back to the
     -- original ring !!
     R := ring I;
     scan (gens R, (v -> v = local v));
     CoeffR := coefficientRing R;
     S := CoeffR[delta];
     return sub(kernel map (R/I,S), R);
     )
