-- Benchmark and Test Suite for Binomials.m2

load "Binomials.m2"
load "Markov.m2"

-- non-radical CI - ideal:
R = markovRing(2,2,2,2);
S = {{{1},{3},{2,4}},
     {{2},{4},{1,3}},
     {{3},{4},{1,2}}};
I = markovIdeal (R,S);
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
if intersect bpd != I then error "Computation wrong!";

-- random example
Q = QQ[c,d,x,y,z,w];
I = ideal(x^3*d^2*w-c*z^2,x^5*y^2-w^7,w^3-z^8,z^2-d*w*x^7)
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
if intersect bpd != I then error "Computation wrong!"; 

-- I22 commuting birth and death ideal 
S = QQ[R00,U00,R01,D01,U01,R02,D02,R10,L10,U10,R11,L11,D11,U11,R12,L12,D12,L20,U20,L21,D21,U21,L22,D22];
I = ideal (U00*R01-R00*U10,R01*D11-D01*R00,D11*L10-L11*D01,L10*U00-U10*L11,U01*R02-R01*U11,R02*D12-D02*R01,D12*L11-L12*D02,L11*U01-U11*L12,U10*R11-R10*U20,R11*D21-D11*R10,D21*L20-L21*D11,L20*U10-U20*L21,U11*R12-R11*U21,R12*D22-D12*R11,D22*L21-L22*D12,L21*U11-U21*L22);
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
if intersect bpd != I then error "Computation wrong!"; 

quit;

