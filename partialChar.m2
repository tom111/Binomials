partialCharacter = (I) -> (
     ts := entries gens I;
     vs := {};
     cl := {};
     for t in ts#0 do (
	  vs = vs | {((exponents (t))#0 - (exponents (t))#1)};
     	  coeffs := entries ((coefficients(t))#1);
-- I hope that coefficients returns the leading coeff as 0th
	  cl = cl | {coeffs#1#0 / coeffs#0#0}
	  );
--    print coeffs;
--    print cl;
     return (transpose matrix vs , cl);
     )

