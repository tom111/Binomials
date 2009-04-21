-- M2 Examples for binomial Ideals
-- Load this to get started

load "Binomials.m2"

R = QQ[x,y]
I = ideal (x^3 - 1, y^5-1)
J = trim intersect BinomialAssociatedPrimes I

-- Here are some more examples

-- R = QQ[x1,x2,x3,x4,x5]
-- I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6)
-- -- Here is a cellular decomp  of I:
-- -- This is also a primary decomposition
-- J1 = ideal({x1^2 , x1*x4^2 - x2*x5^2, x2^5, x5^6, x2^4 * x4^2,x4^8})
-- J2 = ideal({x1*x4^2 - x2*x5^2, x1^3*x3^3 - x4^2*x2^4, x2^3*x4^4 - x1^2*x3^3*x5^2, x2^2*x4^6 - x1*x3^3*x5^4, x2*x4^8 - x3^3 *x5^6 })
-- 
-- 
-- Q = QQ[x,y,z]
-- J = ideal(x^4*y^2-z^6,x^3*y^2-z^5,x^2-y*z)
-- The cellular decomposition is also a primary decomposition.
-- No lattice needs to be saturated, only roots of monomials

-- Here is a constructed example where the saturations take only values in QQ:
-- R = QQ[a,b,c,d];
-- I = ideal (a^2-b^2, b^3-c^3);
-- testCellular I
-- bp = BinomialPrimaryDecomposition I
-- testPrimary \ bp
-- intersect bp == I
 
-- Here is a nontrivial example, the first component of the
-- cellular decomposition is not primary
-- R = QQ[a,b,c]
-- I = ideal(a-b^5,a^2-c,b^2-c^3,c^2-a*b)

-- Q = QQ[x,y,z,w]
-- J = ideal(x^4*w^2-z^6,x^3*y^2-z^5,x^7-y^3*w^2,x^2*x^3-z^7)
-- cd = binomialCD(J); I = cd#0;
-- pc = partialCharacter(I)
-- satpchar(Q,pc#1,pc#2)

-- A fun example, not to small, not too big, but with some
-- nasty features
--   Q = QQ[x,y,z,w];
--   J = ideal(x^3*y^2-z^2,x^5*y^2-w^7,w^3-z^8);
--   cd = binomialCD J; 
--   I = cd#0;
--   pc = partialCharacter cd#0;
--   print ( testPrimary \ cd);

-- Is the following a bug or does it only take very long ????
-- Appearently it has to do with the SY Strategy for Primdec Failing
-- Q = QQ[x,y,z,w]
-- I = ideal (x^3*y^2-z^2, w^7-x^2*z^2, x*y^2*z^4*w^4-1); 
-- time isPrime I;


-- In the following example cd#1 is not primary, but the radical is prime.
-- Q = QQ[c,d,x,y,z,w];
-- I = ideal(x^3*d^2*w-c*z^2,x^5*y^2-w^7,w^3-z^8,z^2-d*w*x^7)
-- cd = binomialCD I

