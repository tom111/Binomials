BinomialSolve = (I,varname) -> (
     -- Solves a zero dimensional pure difference binomial ideal by
     -- constructing the apropriate cyclotomic field
     -- Make an Option to name the variable for the roots of unity.
     
     varname = value varname;
          
     R := ring I;
     RLex := newRing(R,MonomialOrder => Lex);
     if not dim I == 0 then error "Ideal to solve is not zero dimensional";
     
     -- First we need a Lex Groebner Basis of our ideal.     
     groeb := flatten entries gens gb sub(I,RLex);
     
     -- We compute the lcm of the exponents to determine the smallest 
     -- root of unity to adjoin
     
     ex := {};
          
     apply (groeb, (t -> (
     	       	    ex = ex | flatten exponents t;	       	    		    
		    )));
     -- need to strip zeros:
     lce := lcm toList (set ex - set ({0}));
     
     print "Lex Groebner Basis is :";          
     print groeb;
     
     print "Least common exponent is:";
     print lce;
     
     S := QQ[varname];
     Mon := monoid flatten entries vars R;
     C := cyclotomicField(lce,S);
     RSOL = C Mon;

     -- So RSol is a polynomial ring over QQ[zeta] for a good choice
     -- of zeta now
     
     -- Next we have to construct the list of solutions from the GB
     
     )