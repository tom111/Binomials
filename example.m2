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
restart
R = QQ[x1,x2,x3,x4,x5];
I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6);
toString BCD I
cd = binomialCellularDecomposition(I,returnCellVars=>true); toString cd
ap = binomialAssociatedPrimes I; toString ap;
intersect (ap#0,ap#1) == I
binomialRadical I == intersect (ap#0,ap#1)
isCellular (ap#0, returnCellVars=>true)
isCellular (ap#1, returnCellVars=>true)
bpd = BPD I


-----
Q = QQ[x,y,z]
J = ideal(x^4*y^2-z^6,x^3*y^2-z^5,x^2-y*z)
-- The cellular decomposition is also a primary decomposition.
-- No lattice needs to be saturated, only roots of monomials
cd = BCD J
bpd = BPD J

-- Here is a constructed example
R = QQ[a,b,c,d];
I = ideal (a^2-b^2, b^3-c^3);
isCellular I
bp = binomialPrimaryDecomposition I
intersect bp == sub(I,ring bp#0)
mingens intersect bp

--A fun example, not to small, not too big, but with some
-- nasty features. BPD is competetive here.
Q = QQ[x,y,z,w];
J = ideal(x^3*y^2-z^2,x^5*y^2-w^7,w^3-z^8);
time bpd = BPD J; 
time primaryDecomposition J;
I = cd#0;
-- The toric component has an embedded prime!

-- Another example where BPD is too slow
restart
Q = QQ[c,d,x,y,z,w];
I = ideal(x^3*d^2*w-c*z^2,x^5*y^2-w^7,w^3-z^8,z^2-d*w*x^7)
time cd = BCD I;
time bpd = BPD I;
time primaryDecomposition I;
intersect cd == I
intersect bpd == I

