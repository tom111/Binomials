-- New algorithms for cellular decomposition of binomial ideals
load "FourTiTwo.m2"
load "Binomials.m2"

-- R = QQ[x1,x2,x3,x4,x5]
-- I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6)
-- Here is a cellular decomp  of I:
-- This is also a primary decomposition

-- bcd = oldBCD I;
-- tor = toricMarkov(transpose syz transpose (partialCharacter(I, cellVariables => gens R))#1,R )
-- rest = saturate(I,tor)

isMonomial = p -> (
     if #(terms p) <= 1 then return true
     else return false;
     )

toricComponent = I -> (
     R := ring I;      
     A := transpose syz transpose (partialCharacter(I, cellVariables => gens R))#1;
     tor := toricMarkov(A,R);
     return tor
     )

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


geomCD2 = I -> (
     -- Combine geometric decompo with computing the toric component first
     R := ring I;
     A := transpose syz transpose (partialCharacter(I, cellVariables => gens R))#1;
     tor := toricMarkov(A,R);
     return {tor} | oldBCD (I:tor)
     )

-- Cellular decomposition of binomial ideals:

BCD = (I) -> (
     -- New algorithm based on the exhaustive usage of 4ti2
     
     -- ToDo : Check for monomials:
     R := ring I;
     A := transpose syz transpose (partialCharacter(I, cellVariables => gens R))#1;
     tor := toricMarkov(A,R);
     return {tor} | oldBCD (I:tor)
     )

BCD2 = (I) -> (
     -- New algorithm based on the exhaustive usage of 4ti2
     
     -- ToDo : Check for monomials:
     R := ring I;
     A := transpose syz transpose (partialCharacter(I, cellVariables => gens R))#1;
     tor := toricMarkov(A,R);
     return {tor} | oldBCD (saturate(I,tor))
     )

oldBCD = (I) -> (
-- By Ignacio Ojeda and Mike Stillman     
-- Comments by TK
     R := ring I;
     n := numgens R;
     Answer := {};
     L := null;
     IntersectAnswer := ideal(1_R);
     ToDo := {{1_R,toList(0..n-1),I}};
     -- Each entry of the ToDoList is a triple:
     -- #0 contains 
     -- #1 contains variables to be considered for cell variables
     -- #2 is the ideal to decompose
     compo := 0;
     next := () -> (
	 if #ToDo === 0 then false
	 else (
--	      << "The remaining Todolist: " << toString ToDo << endl; 
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
		   Answer = append(Answer,newone);
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
--			<< "A division was needed, adding x_i to power " << k << " " << endl;
     	       	    	-- We add the monomial i^k to ideal under consideration		      	   	
			J2 = L#2 + ideal(R_i^k); 
     	       	    	-- And remove L#0 components from variables that we already
			-- considered before
			J2 = saturate(J2, L#0);
			if J2 != ideal(1_R) then
			    -- If something is left after removing we have more to decompose J2
			    ToDo = prepend({L#0, newL1, J2},ToDo));
		       -- Continue with the next variable and add i to L#0
		   if J != ideal(1_R) then (
--			<< "Adding I:x_i" << endl;
			ToDo = prepend({R_i * L#0, newL1, J},ToDo);
			);
		   );
	      true));
     while next() do ();
     Answer	      
     )

SetSat = (I,E) -> (
     
     error "THIS IS BROKEN. Don't use it.";
     
     -- Will compute the ideal I_E = I + M(E) : (\prod_{e\inE}
     -- x_e)^\infty as defined on p.41 in ES96 using 4ti2.
     
     -- Check that we have no coefficients
     if not isPureDifference I then error "Not implemented, sorry";
          
     R := ring I;
     scan (gens R, (v -> v = local v));
     CoeffR := coefficientRing R;
     Ec := toList (set gens R - set E);
     M := sub (ideal Ec, R);
     I2 := I + M;
     mgI2 := flatten entries mingens I2;     
     -- Find the nilpotent variables mod I+M
     mongens := for m in mgI2 list if (#terms m) == 1 then m else continue;
     print mongens;
     hugemon := 1_R;
     if #mongens>0 then hugemon = product mongens;
          
     notnil := for v in gens R list if hugemon % v != 0_R then v else continue;
     print notnil;
     nilvars := toList (set gens R - set notnil);
     print nilvars;
     S := CoeffR[notnil];
     J := kernel map (R/I2,S);
     pc := partialCharacter(J, cellVariables => notnil);
     A := pc#1;
     Jsat := toricMarkov (transpose A, S, InputType => "lattice");
     return sub(ideal nilvars , R) + Jsat;
     )


