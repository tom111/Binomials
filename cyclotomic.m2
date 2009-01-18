cyclotomicField = (i,v) -> (
     R := QQ[v];
     return R / sub (ideal(cyclotomicPoly (i,v)) ,R);
     )

-- Inverting Roots manually
-- cycloInverse = ()    


cyclotomicPoly = (i,v) -> (
     -- returns the i-th cyclotomic polynomial in variable v.
     if i <= 0 then error "the input should be > 0.";
     v1=v;
     if i==1 then return v1-1 ;
     min := v1^i -1;
     -- dividing out the first cylcotomic polynomial
     -- (with result a polynomial)
     min = (flatten entries syz matrix {{min ,(v1-1)}})#1; 

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
