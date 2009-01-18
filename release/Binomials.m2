newPackage(
	"Binomials",
    	Version => "0.1", 
    	Date => "January 2009",
    	Authors => {
	     {Name => "Thomas Kahle", Email => "kahle@mis.mpg.de", HomePage => "http://personal-homepages.mis.mpg.de/kahle/"}},
    	Headline => "Spezialised routines for binomial Ideals",
	Configuration => { "doNumerics" => false },
    	DebuggingMode => true
    	)
   
export {binomialCD,
     partialCharacter,
     testCellular,
     cellVars,
     Lsat,
     idealFromCharacter,
     saturatePChar,
     saturatePCharNum,
     BinomialSolve,
     satIdeals,
     testPrimary,
     BinomialAssociatedPrimes,
     CellularBinomialPrimaryDecomposition,
     BPD,
     testPrime,
     BinomialRadical,
     makeBinomial,
     nonCellstdm,
     maxNonCellstdm,
     BCDisPrimary,
     isBinomial,
     minimalPrimaryComponent,
     lcm,
     binomialQuasiPower,
     BinomialQuotient,
     projectToCellRing,
     removeRedundant,
     -- Options
     cellVariables, -- for partialCharacter
     returnPrimes -- for testPrimary 
     }

needsPackage "SingSolve";

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
     next := () -> (
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
Lsat = A -> syz transpose syz transpose A;

testCellular = I -> (
     R := ring I;
     cv := cellVars I;
     if cv == {} then prod := 1_R else prod = product cv;
     if I == saturate (I, prod) then return true
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
     
     -- print o.cellVariables;
     -- The input should be a cellular ideal 
     if o#cellVariables === null then (
	  -- No cell variables are given -> compute them
	  cellvars := cellVars(I);
	  )
     else cellvars = o#cellVariables;
     
     -- If there are no cellular variables, 
     -- the ideal is monomial and the partial character is zero:
     if cellvars == {} then (
	  return ({}, matrix "0", {1});
	  );
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     CoeffR := coefficientRing R;
     S := CoeffR[cellvars];
     II := kernel map (R/I,S);

     -- The partial Character of the zero ideal is the 
     -- zero lattice.       
     if ( II == 0 ) then (
	  for i in gens ring II do vs = vs | { 0_ZZ };
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
     return (cellvars, transpose matrix vs , cl);
     )

isBinomial = I -> (
     ge := flatten entries gens I;
     for g in ge do (
          if #(terms g) > 2 then return false;	  
	  );
     return true;
     )
     
cellVars = I -> (
     cv := {};
     for i in gens ring I do if saturate (I,i) != substitute(ideal(1), ring I) then cv=cv|{i};
     return cv;
     )

nonCellstdm = I -> (
     -- Extracts the monomials in the non-Cell variables.
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

maxNonCellstdm = I -> (
     -- Extracts the Maximal elements in the set of monomials 
     nm := nonCellstdm I;
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
     -- exponent vector m and coefficient c in the R
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
     
     -- We coerce the coefficients to R:
     c = apply (c, a -> (sub (a,R)));
      
     cols := entries transpose A;
     binomials := for i in 0..numcols A-1 list makeBinomial (R,cols#i, c#i);

     -- If the coefficients are all "1". Can we use 4ti2 here?
     -- TODO: This saturation will typically fail if 
     -- we have complex coefficients :(
     
     -- At least if A is the unit matrix we are done.
     idmat := matrix mutableIdentity(ZZ,#var);
     if A == idmat then return ideal binomials;
     
     -- Otherwise a saturation may be needed.  
     -- print "Warning ! This step possibly does not terminate !";
     return saturate (ideal binomials, product var);
     )

saturatePCharNum = (va, A, c) -> (
     -- This function saturates a partial character numerically.
     -- This is pretty useless.
     
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
     Q := QQ[varlist / value];
     eqs := idealFromCharacter(Q,K,c);
     
     print "The character defining equations are:";
     print eqs;
     -- print ring eqs;
     
     -- Is this saturation needed ??
     eqso := eqs;
     eqs = saturate(eqs, product gens ring eqs);
     if eqso == eqs then print "Saturation was not needed !" 
     else print "!!!!!!! Saturation was needed - this is a bug  !!!!!!!!";
     
     -- And solve using singsolve:
     print "Warning, using numerics !!!.";
     result = singsolve eqs;
     return (va, S, result);
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
     Q := QQ[varlist / value];
     eqs := idealFromCharacter(Q,K,c);
     
     print "The character defining equations are:";
     print eqs;
     -- print ring eqs;
     
     -- We carefully(tm) clear denominators:
     -- Is this saturation needed ??
     eqso := eqs;
     eqs = saturate(eqs, product gens ring eqs);
     if eqso == eqs then print "Saturation was not needed !" 
     else print "!!!!!!! Saturation was needed - this is a bug  !!!!!!!!";

     result = BinomialSolve eqs;
     return (va, S, result);
     )

BinomialSolve = I ->(
     -- Should find the solutions to the pure binomial system 
     -- and construct a cyclotomic field in which all exist.
     -- Currently it will set to zero everything that is not 
     -- in QQ.
     print "Currently we run Singular and parse the result";
     sols := singsolve I;
     for sol in sols do(
	  for entry in sol do(
	       entry = sub (entry, QQ);
	       );
	  );
     return sols;
     )
     

satIdeals = (va, A, d) -> (
     -- computes all the ideals belonging to saturations of 
     -- a given partial character.
     satpc = saturatePChar(va, A, d);
     -- The following should be the smallest ring 
     -- containing all new coefficients
     Q := QQ[satpc#0];
     satideals = apply (satpc#2 , (c) -> (
	       -- print {Q, satpc#1, c};
	       idealFromCharacter(Q,satpc#1,c)));
     return satideals;
     )

BinomialRadical = I -> (
     if not testCellular I then error "Input was not cellular.";
     -- Computes the radical of a cellular binomial ideal
     R := ring I;
     -- Get the partial character of I
     pc := partialCharacter(I);
     noncellvars := toList(set (gens R) - pc#0);
     
     M := sub (ideal (noncellvars),R);
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     CoeffR := coefficientRing R;
     S := CoeffR[pc#0];
     -- The the radical missing the monomials:
     prerad := kernel map (R/I,S);
     return sub (prerad ,R) + M;
     )

testPrimary = method (Options => {returnPrimes => false})
testPrimary Ideal := Ideal => o -> I -> (
     -- Implements Alg. 9.4 in [ES96]
     -- I must be a cellular ideal
     -- Returns the radical of I and whether I is primary
     -- if the option returnPrimes is true, then it will return 
     -- the radical in the affirmative case and two distinct associated primes
     -- otherwise
     
     -- this test is expensive ...
     -- if not testCellular I then error "Input was not cellular.";
     -- The ring of I :
     R := ring I;
     
     -- Only proper ideals are considered primary
     if I == ideal(1_R) then return false;      
     
     -- Get the partial character of I
     pc := partialCharacter(I);
     noncellvars := toList(set (gens R) - pc#0);
     
     M := sub (ideal (noncellvars),R);
     -- print ("The monomial ideal M: " | toString M);
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     CoeffR := coefficientRing R;
     S := CoeffR[pc#0];
     -- The the radical missing the monomials:
     prerad := kernel map (R/I,S);
     -- print prerad;
     
     rad := sub (prerad ,R) + M;
     -- print "The radical is:";
     -- print rad;
     
     -- If the partial character is not saturated, the radical is not prime
     if image Lsat(pc#1) != image pc#1 then (
	  print "The radical is not prime, as the character is not saturated";
	  if o#returnPrimes then (
	       satpc := saturatePChar pc;
	       ap1 := sub (idealFromCharacter (S,satpc#1,satpc#2#0), R) + M;
	       ap2 := sub (idealFromCharacter (S,satpc#1,satpc#2#1), R) + M;
	       -- Return two distinct associated primes:
	       return {ap1,ap2};
     	       )	   	       
	  else return false;
	  );
     
     -- The list of maximally standard monomials:
     maxstdmon := maxNonCellstdm I / (i -> sub (i,R));
     -- print "The maximally standard monomials are:";
     -- print maxstdmon;
     
     for m in maxstdmon do (
	  q := quotient (I, m);
	  -- Mapping down to cellvars:
	  q2 := kernel map (R/q,S);
     	  -- I_+(sigma) was called prerad above:
	  if not isSubset(q2, prerad) then (
	       -- print ( "not primary! A monomial is: " | toString m);
	       if o#returnPrimes then (
		    qchar := partialCharacter q;
		    satqchar := saturatePChar qchar;
		    ap2 := idealFromCharacter (S,satqchar#1,satqchar#2#0);
		    return {rad, sub(ap2,R) + M};
     	       	    )		    
	       else return false;
	       );
	  );
     -- print "Ideal is primary";
     if o#returnPrimes then return {rad}
     else return true;	  
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
     
BinomialAssociatedPrimes = (I) -> (
     -- Computes the associated primes of cellular binomial ideal
     
     -- Disabling the check for a while, it's too time consuming
     -- if not testCellular I then error "Input was not cellular.";     
     R := ring I;
     cv := cellVars(I); -- cell variables E
     -- print "Cellvars:"; print cv;
     primes := {}; -- This will hold the list of primes
     ncv := toList(set (gens R) - cv); -- non-cell variables x \notin E
     -- print "Noncellvars"; print ncv;
     ml := nonCellstdm(I); -- List of std monomials in ncv
     -- Coercing to R:
     ml = ml / ( m -> sub (m,R) );
     -- print ml;
     -- The ring k[E]:
     CoeffR := coefficientRing R;
     S := CoeffR[cv];
     prerad := kernel map (R/I,S);
     -- The primes will live in a complex ring... 
     -- Maybe later. For now they will ive in R
     -- CR = CC[gens R];
     --M := sub (ideal (ncv),CR); -- The monomial radical ideal
     M := sub (ideal (ncv),R); -- The monomial radical ideal
     -- A dummy ideal and partial Characters:
     Im := ideal;
     pC := {}; sat = {};
     for m in ml do (
	  -- print m;
	  Im = kernel map (R/(I:m),S);
	  -- We already know the cell variables in the following computation
	  pC = partialCharacter(Im, cellVariables=>cv);
	  sat = satIdeals(pC);
	  -- Coercing back to R: 
	  -- needed ??
	  sat = sat / (I -> sub (I,R));
	  sat = sat / (I -> I + M);
	  -- adding result and removing duplicates
	  if isSubset ({sat}, primes) then continue;
	  primes = primes | toList set sat;
	  );
     return toList set primes;
     )

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

minimalPrimaryComponent = I -> (
     -- Input a cellular binomial ideal whose radical is prime.
     -- Ouptut, generators for Hull(I)
     
     ap := testPrimary (I, returnPrimes=> true);
     if #ap == 1 then return I
     else (
	  R := ring I;
	  -- The radical:
     	  J1 := ap#0; -- = BinomialRadical I;
	  J2 := ap#1;
     	  pc1 := partialCharacter J1;
	  pc2 := partialCharacter J2;
	 
	  -- ap#0 and ap#1 correspond to 
	  -- distinct lattices L1 and L2
	  L1 := image pc1#1;
	  L2 := image pc2#1;

     	  -- For debugging, this will output ideals and characters:	  
--	  print J1;
--	  print pc1;
--	  print "------------";
--	  print J2;
--	  print pc2; 
	  
	  L = intersect {L1,L2};
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
	       return minimalPrimaryComponent BinomialQuotient (I,b);
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
	    	 return minimalPrimaryComponent BinomialQuotient (I,b);
	    	 );
	    ) -- else path of if not testPrimary
     ) -- minimalPrimaryComponent

BinomialQuotient = (I,b) -> (
     -- Algorithm A.3 in Ojeda / Sanchez
     -- Input I - Cellular Binomial Ideal 
     -- b -- Binomial in the cell variables of I which is a zerodivisor mod I
     -- Output : The quotient (I : b^[e]) for a suitably choosen e, such that the
     -- result is binomial
     
     R := ring I;
     cv := cellVars (I);
     
     --First check if we can save a lot of time if already I:b is binomial,
     -- and no quasipowers have to be taken.
     quot :=  quotient (I , sub(ideal(b),R));
     if isBinomial quot then return quot;
          
     --Transporting the standard monomials to R:
     ncvm := ((i) -> sub (i,R) ) \ nonCellstdm I ;
     -- print ncvm;
  
     U' := {}; -- U' as in the paper
     D  := {};
     J := ideal (0_R); -- initialize with zero ideal
     bexp := (exponents b)#0 - (exponents b)#1; -- exponent vector of b
     -- We will often need the image of bexp, so lets cache it
     bexpim := image transpose matrix {bexp};
     pc := {}; -- Will hold partial characters;
     CoeffR := coefficientRing R;
     S := CoeffR[cv]; -- k[\delta] in the paper
     
     for m in ncvm do(
	  quot = I:m;
	  	  
	  -- Mapping to k[delta] and taking character
	  quot = kernel map (R/quot, S);
	  pc = partialCharacter quot;
	  
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

lcm = l -> (
     if #l == 0 then return 1;
     sublcm := lcm delete (l#0,l);
     return l#0 * sublcm / gcd (l#0, sublcm);
     )

binomialQuasiPower = (b,e) -> (
     -- returns the e-th quasipower of the binomial b
     -- i.e. (b_1)^e - (b_2)^e
     return ((terms b)#0)^e - (- (terms b)#1)^e;
     )

BPD = I -> (
     -- The full binomial primary decomposition 
     -- starting from a not necessarily cellular binomial ideal
     cd := binomialCD I;
     counter := 1;
     cdc := #cd;
     bpd := {};
     scan (cd , ( (i) -> (
	   	    print ("Decomposing cellular component: " | toString counter | " of " | toString cdc);
		    counter = counter +1;
--		    print i;
--		    print CellularBinomialPrimaryDecomposition i;
		    bpd = bpd | CellularBinomialPrimaryDecomposition i;
		    )
	       )
    	  ); -- apply
     -- print bpd;
     print "Removing redundant components (fast)";
     return removeRedundant bpd;
     )
     
CellularBinomialPrimaryDecomposition = I -> (
     -- computes the binomial primary decomposition of a cellular ideal
     -- I needs to be cellular 
     -- Implements algorithm 9.7 in ES96, respectively A5 in OS97
     R := ring I;
     ap := BinomialAssociatedPrimes I;
     -- Projecting down the assoc. primes, removing monomials
     -- TODO: Don't compute cell variables twice, thrice,...
     pap := ap / projectToCellRing;
     -- Lifting back the result to R:
     pap = pap / ((P) -> sub(P,R));
     -- Compute and return minimal primary Components:
     return pap / ( (P) -> minimalPrimaryComponent (I + P));
     )

removeRedundant = l -> (
     -- Removes redundant components from a list of ideals to be intersected
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

projectToCellRing = I -> (
     -- projects a cellular ideal down to the ring k[\delta]
     -- where delta is the set of cell variables
     R := ring I;
     cv := cellVars I;
          -- Extracts the monomials in the non-Cell variables.
     -- We map I to the subring: k[ncv]
     CoeffR := coefficientRing R;
     S := CoeffR[cv];
     return kernel map (R/I,S);     
     )

