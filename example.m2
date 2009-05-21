-- M2 Examples for binomial Ideals
-- Load this to get started

load "Binomials.m2"

-- This demonstrates the not so nice features when the coefficient
-- field is extended
R = QQ[x,y]
I = ideal (x^3 - 1, y^5-1)
ap = binomialAssociatedPrimes I
print (toString \ ap);
J = intersect ap;
mingens J
gens gb J

-- Here are some more examples

-- Example from Eisenbud/Sturmfels
R = QQ[x1,x2,x3,x4,x5]
I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6)
-- Here is a cellular decomp  of I:
-- This is also a primary decomposition
J1 = ideal({x1^2 , x1*x4^2 - x2*x5^2, x2^5, x5^6, x2^4 * x4^2,x4^8})
J2 = ideal({x1*x4^2 - x2*x5^2, x1^3*x3^3 - x4^2*x2^4, x2^3*x4^4 - x1^2*x3^3*x5^2, x2^2*x4^6 - x1*x3^3*x5^4, x2*x4^8 - x3^3 *x5^6 })
intersect (J1,J2) == I

Q = QQ[x,y,z]
J = ideal(x^4*y^2-z^6,x^3*y^2-z^5,x^2-y*z)
-- The cellular decomposition is also a primary decomposition.
-- No lattice needs to be saturated, only roots of monomials
cd = BCD J
bpd = BPD J

-- Here is a constructed example
-- This does not work as of May 2009
R = QQ[a,b,c,d];
I = ideal (a^2-b^2, b^3-c^3);
isCellular I
bp = binomialPrimaryDecomposition I
testPrimary \ bp
intersect bp == I

--A fun example, not to small, not too big, but with some
-- nasty features
Q = QQ[x,y,z,w];
J = ideal(x^3*y^2-z^2,x^5*y^2-w^7,w^3-z^8);
cd = BCD J; 
I = cd#0;
-- partial character is now an internal function
-- pc = partialCharacter cd#0;
print ( testPrimary \ cd);

-- Is the following a bug or does it only take very long ????
-- Appearently it has to do with the SY Strategy for Primdec Failing
Q = QQ[x,y,z,w]
I = ideal (x^3*y^2-z^2, w^7-x^2*z^2, x*y^2*z^4*w^4-1); 
time isPrime I;

-- In the following example cd#1 is not primary, but the radical is prime.
-- This functionality is not yet implemented !
Q = QQ[c,d,x,y,z,w];
I = ideal(x^3*d^2*w-c*z^2,x^5*y^2-w^7,w^3-z^8,z^2-d*w*x^7)
cd = BCD I
bpd = BPD I
intersect cd == I
intersect bpd == I
