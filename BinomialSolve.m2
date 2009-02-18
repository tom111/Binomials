load "cyclotomic.m2"
load "Binomials.m2"
R = QQ[a,b,c];
I = ideal (b^2-a,a^2-c,c^2-b);

-- We solve such equations using modulo 1 arithmetics.  The basic task
-- is to solve a^n = 1^{k/m}, whose solutions are the equivalence
-- classes of: k/nm, 1/n + k/m, 2/mn + k/nm,... , (n-1)/n + k/nm
          
-- The following function implements this:
Rooter = (n,q) -> (
     -- INPUT:
     -- n an integer
     -- q a rational number between zero and one representing k/m
     -- OUTPUT:
     -- The list of root-exponents:
     -- k/nm, 1/n + k/m, 2/mn + k/nm,... , (n-1)/n + k/nm
     k := 0/1;
     m := 1;
     if q != 0 then (
	  m = denominator sub(q,QQ);
	  k = numerator sub(q,QQ);
	  );
     val := 0;
     roots := for i in 0..n-1 list (
	  val = i/n + k/(n*m);
	  if val > 1 then val = val - floor val;
	  val
	  );
     return roots;
     );

SolveMore = (binom,psol) -> (
     -- This function extends a partial solution further
     -- INPUT: A partial solution and a binomial which after plugging
     -- in the partial solutions is univariate
     -- OUTPUT: An extended partial solution

     print "Entering function SolveMore";     
     print psol;
     print binom;
     
     -- Since Lex is a global order the true monomial comes first, right ?
     mon := (terms binom)#0; -- The monomial in the new variable.
     
     -- we need the index of the variable that we will solve now
     -- <incomprehensable hack>
     ind := index (flatten entries gens radical monomialIdeal mon)#0;
     var := (flatten entries gens radical monomialIdeal mon)#0;
     -- </incomprehensable hack>

     rhs := (terms binom)#1; -- The right hand side which is a power
			     -- of a root of unity
     erhs := flatten exponents rhs;
     
     newsols := {}; -- A list accumulating extended solutions
      
     -- If the binomial contains a common variable in both of its
     -- monomials then zero is a solution for this variable We are
     -- looking at erhs at position ind to determine this case
     
     roots := {};
     
     rhsvarpow := erhs#ind;
     
     if rhsvarpow > 0 then (
	  -- zero is a solution for variable ind
	  -- We fork of a new solution with entry "n" and divide by 
	  -- the offending variable
	  roots = {"n"};
     	  mon = lift(mon / var^rhsvarpow, ring mon);
	  rhs = lift(rhs / var^rhsvarpow, ring rhs);
	  erhs = flatten exponents rhs;
      	  );

     emon := flatten exponents mon;
     -- one element list containing the exponent
     n := (toList (set emon - set {0}))#0; 

      -- This needs to be done for each entry in psol:
      for onesol in psol do (
	   roots = {};
	   -- now determine the right hand side exponent from the
	   -- partial solutions.
	   zeroflag := false;    
       	   q := for v in 0..#erhs-1 list (
		-- First case: variable does not appear -> exponent 0
		if (erhs#v == 0) then 0
		else if onesol#v === "n" then (
		     -- if erhs > 0 and onesol has a "n", then the rhs is zero!
     	       	     zeroflag = true;
		     break 
		     )
		-- otherwise exponent times old exponent
		else erhs#v * onesol#v
		);
	   
	   if zeroflag and #roots == 0 then (
		roots = roots | {"n"};
		)
	   else (
		if not zeroflag then q = sum q;
		);
	   -- print q;
     	       
       	   -- now everthing is set for the Rooter:
       	   roots = roots | Rooter (n,q);
       	   extensions := for r in roots list (
	    	for i in 0..#onesol-1 list if i==ind then r else onesol#i
	    	);
       	   newsols = newsols | extensions;
       	   );
      
      print "Leaving Function SolveMore";
      print newsols;
      
      
      return newsols;	  
      )
 
BinomialSolve = (I, varname) -> (
     R := ring I;
     cd := binomialCD I;
     exponentsols = flatten for c in cd list CellularBinomialExponentSolve c;
     
     -- print exponentsols;
     -- determine the least common denominator, ignoring nulls
     denoms := for i in flatten exponentsols list if i =!= null then denominator i else continue;
     -- print denoms;
     -- If there are no denominators, the ideal was monomial
     -- and we return only (0,0,...,0)
     if denoms === {} then return {for i in gens R list 0};
     lcd = lcm denoms;
     print lcd;

     -- This is our standard. Coefficients are rational?
     C := QQ;     
     print describe C;
     if lcd > 2 then (
	  print "Adjoining roots of unity is needed";
	  ww = value varname;
     	  S := QQ[ww];
     	  Mon := monoid flatten entries vars R;
     	  C = cyclotomicField(lcd,S);
	  );
     
     print describe C;
     
     print ww^3;
     
     
     expo = q -> (
     -- This inline function maps a quotient from QQ to its element in S	  
	  if q === null then return 0_C;
	  if q == 0 or q == 1 then return 1_C;
	  if q == (1/2) then return -1_C;
	  k := numerator sub(q,QQ);
	  m := denominator sub(q,QQ);
	  if m != lcd then k = k * sub(lcd / m,ZZ);
	  return sub(ww^k,C);
	  );
     
     print exponentsols#2;
     print exponentsols#3;
     sols = flatten exponentsols;
     print sols#0;
     sols = expo \ sols;
     sols = pack (#(gens ring I),sols);
     print sols#2;
     print sols#3;
     
     
     print ("BinomialSolve created a cyclotomic field by adjoining a " | toString lcd | "th root of unity"); 
     
     print ("This root is called " | toString ww ); 
     
     -- Removing duplicates
     -- This should not be necessary
--      todo := sols;
--      result = {};
--      while #todo > 0 do (
-- 	  result = result | todo#0;
-- 	  cur = todo#0;
-- 	  -- print cur;
-- 	  todo = for t in todo list if t != cur then t else continue;
--      	  );
--      
     return sols; 
     )

CellularBinomialExponentSolve = I -> (
     -- Solves a zero dimensional cellular pure difference binomial
     -- ideal by constructing the apropriate cyclotomic field
     
     R := ring I;
     varlist := flatten entries vars R;
     RLex := newRing(R,MonomialOrder => Lex);
     if not dim I == 0 then error "Ideal to solve is not zero dimensional";
     
     -- First we need a Lex Groebner Basis of our ideal.     
     groeb := flatten entries gens gb sub(I,RLex);
     
     print "This is the Groebner basis. Is it ordered correctly ??";
     print groeb;
          
     -- The data structure for a partial solution is as follows: It is
     -- a list of n-tuples where n is the number of variables. These
     -- tuples contain either rational numbers at already solved
     -- positions or the symbol '*' indicating that this position is
     -- unsolved and the special symbol null indicating that the
     -- solution(not exponent) is zero

     -- For each variable we check if it is a non-cell variable, ie 
     -- each solution of the ideal has coordinate zero there
     psols := for v in varlist list if saturate(I,v) != I then null else "*"; 

     -- make it a proper list of solutions
     psols = {psols};

     -- We solve on a log-scale for the exponents
     while #groeb > 0 do (
	  -- check if the current term is a binomial
	  if #(exponents groeb#0) > 1 then (
	       psols = SolveMore(groeb#0, psols);
	       );
     	  groeb = drop(groeb, 1);
	  );
     
     return psols;
     
     )