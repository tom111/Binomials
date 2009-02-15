BinomialSolve = I -> (
     -- Solves a zero dimensional pure difference binomial ideal by
     -- constructing the apropriate cyclotomic field
     -- Make an Option to name the variable for the roots of unity.
     
     symb := "ww";
          
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
     
     -- Construct the Cyclotomic field
     CF := QQ[symb];
     print cyclotomicPoly (lce, ww);
               
     -- 
     )