-- Testsuite for Binomials
needsPackage "Binomials";
needsPackage "Markov";

-- nonradical CI
R = markovRing(2,2,2,2); S = {{{1},{3},{2,4}},{{2},{4},{1,3}},{{3},{4},{1,2}}}; I = markovIdeal (R,S);
bpd = binomialPrimaryDecomposition I;
assert (intersect bpd == I); 

-- random example
Q = QQ[c,d,x,y,z,w];
I = ideal(x^3*d^2*w-c*z^2,x^5*y^2-w^7,w^3-z^8,z^2-d*w*x^7)
bpd = binomialPrimaryDecomposition I;
assert (intersect bpd == I); 

-- I22 commuting birth and death ideal 
S = QQ[R00,U00,R01,D01,U01,R02,D02,R10,L10,U10,R11,L11,D11,U11,R12,L12,D12,L20,U20,L21,D21,U21,L22,D22];
I = ideal (U00*R01-R00*U10,R01*D11-D01*R00,D11*L10-L11*D01,L10*U00-U10*L11,U01*R02-R01*U11,R02*D12-D02*R01,D12*L11-L12*D02,L11*U01-U11*L12,U10*R11-R10*U20,R11*D21-D11*R10,D21*L20-L21*D11,L20*U10-U20*L21,U11*R12-R11*U21,R12*D22-D12*R11,D22*L21-L22*D12,L21*U11-U21*L22);
bpd = binomialPrimaryDecomposition I;
assert (intersect bpd == I); 

-- another 'random' example
R = QQ[a..h]
I = ideal(d*g*h-e*g*h,a*b*g-c*f*h,a*b*c-e*g*h,c*f*h^2-d*f,e^2*g*h-d*h,b*d*f*h-c*g,a*d*f*g-c*e,b*c*e*g-a*f,a*b*e*f-c*d);
bpd = binomialPrimaryDecomposition I;
assert (intersect bpd == I); 

-- Cyclotomic stuff
R = QQ[x,y,z]; I = ideal (x^2*y-z^2, x^2-z^3, y^4-1); bpd = BPD I;
assert (intersect bpd == sub(I, ring bpd#0));

-- Unmixed Decomposition
R = QQ[x,y,z];
I = ideal (x^2, y^2, x*y, x*(z^3-1), y*(z^2-1))
bud = BUD I;
assert(intersect bud == I);
assert(dim \ flatten (associatedPrimes \ bud) == {1,0,0,0})

quit();
