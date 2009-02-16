cyclotomicField = (i,R) -> (
     -- Given a ring R, and a power i, the cyclotomic field is returned
     return toField (R / sub (ideal(cyclotomicPoly (i,R_0)) ,R));
     )

-- Inverting Roots manually
-- cycloInverse = ()    

cyclotomicPoly = (i,v) -> (
     -- returns the i-th cyclotomic polynomial in variable v.
     -- v must be a variable a priori
     v = value v;
     if i <= 0 then error "the input should be > 0.";
     if i==1 then return v-1 ;
     min := v^i -1;
     -- dividing out the first cylcotomic polynomial
     -- (with result a polynomial)
     min = (flatten entries syz matrix {{min ,(v-1)}})#1; 

     -- i is prime:
     if isPrime i then return min / (leadCoefficient min);
     
     -- i is not prime:
     -- find the divisors:
     for f in toList (2..i//2) do (
	  -- check for factor
	  if i%f == 0 then (
	       fac := cyclotomicPoly (f,v);
	       -- print fac;
	       -- division with result in polynomial ring:
	       min = (flatten entries syz matrix {{min,fac}})#1;
	       )
	  );
     --make sure the leading coefficient is one.
     min=min / leadCoefficient(min);            
     return(min);                        
)
