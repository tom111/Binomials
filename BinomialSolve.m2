load "cyclotomic.m2"
R = QQ[a,b];
I = ideal (b^3-1,b^2*a^4-b);


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
     	  	  
     -- Since Lex is a global order the true monomial comes first, right ?
     mon := (terms binom)#0; -- The monomial in the new variable.
     	  
      -- we need the index of the variable that we will solve now
      -- <incomprehensable hack>
      ind := index (flatten entries gens radical monomialIdeal mon)#0;
      -- </incomprehensable hack>

      rhs := (terms binom)#1; -- The right hand side which is a power
			      -- of a root of unity
      erhs := flatten exponents rhs;
	  				  
      -- one element list containing the exponent
      n := (toList (set flatten exponents mon - set {0}))#0; 
      print mon, n;
      print psol;
     	  
      newsols := {}; -- A list accumulating extended solutions
     	  	  
      -- This needs to be done for each entry in psol:
      for onesol in psol list (
	   -- now determine the right hand side exponent from the
	   -- partial solutions.
	       
       	   q := for v in 0..#erhs-1 list (
		if (erhs#v == 0) then 0
		else erhs#v * onesol#v
		);
	   print q;
	   q = sum q;
	   print q;
     	       
       -- now everthing is set for the Rooter:
       roots := Rooter (n,q);
       extensions := for r in roots list (
	    for i in 0..#onesol-1 list if i==ind then r else onesol#i
	    );
       newsols = newsols | extensions;
       );
  return newsols;	  
  );



BinomialSolve = (I,varname) -> (
     -- Solves a zero dimensional pure difference binomial ideal by
     -- constructing the apropriate cyclotomic field
     -- Make an Option to name the variable for the roots of unity.
    
     ww = value varname;
          
     R := ring I;
     varlist := flatten entries vars R;
     RLex := newRing(R,MonomialOrder => Lex);
     if not dim I == 0 then error "Ideal to solve is not zero dimensional";
     
     -- First we need a Lex Groebner Basis of our ideal.     
     groeb := flatten entries gens gb sub(I,RLex);
     
     
     -- The data structure for a partial solution is as follows: It is
     -- a list of n-tuples where n is the number of variables. These
     -- tuples contain either rational numbers at already solved
     -- positions or the symbol '*' indicating that this position is
     -- unsolved

     psols := for v in varlist list "*"; -- Saves the list of partial solutions
     
     -- First element of the Groebner basis must be univariate,
     -- i.e of the form (x_i)^n-1
     
     
     solvable := groeb#0;
     drop(groeb, 1);
     
     print "This equation should be univariate:";     
     print solvable;
     
     print SolveMore(b^4-a,{{0,"*"}});
     
    
     

-- Maybe we dont need to create the cyclotomic field     
--      -- Solution for the variable in mon: var = ww	    
--      soldic#varindex = ex;
--      
--           -- We compute the lcm of the exponents to determine the smallest 
--      -- root of unity to adjoin
--      
--      ex := {};
--           
--      apply (groeb, (t -> (
--      	       	    ex = ex | flatten exponents t;	       	    		    
-- 		    )));
--      -- need to strip zeros:
--      lce := lcm toList (set ex - set ({0}));
--      
--      print "Lex Groebner Basis is :";          
--      print groeb;
--      
--      print "Least common exponent is:";
--      print lce;
--      
--      S := QQ[ww];
--      Mon := monoid flatten entries vars R;
--      C := cyclotomicField(lce,S);
--      RSOL = C Mon;
-- 
     
     )