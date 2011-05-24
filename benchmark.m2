-- Benchmark and Test Suite for Binomials.m2
needsPackage "Binomials"
needsPackage "Markov"

-- non-radical CI - ideal:
R = markovRing(2,2,2,2);
S = {{{1},{3},{2,4}},
     {{2},{4},{1,3}},
     {{3},{4},{1,2}}};
I = markovIdeal (R,S);
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
assert (intersect bpd == I); 

-- random example
Q = QQ[c,d,x,y,z,w];
I = ideal(x^3*d^2*w-c*z^2,x^5*y^2-w^7,w^3-z^8,z^2-d*w*x^7)
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
assert (intersect bpd == I); 

-- I22 commuting birth and death ideal 
S = QQ[R00,U00,R01,D01,U01,R02,D02,R10,L10,U10,R11,L11,D11,U11,R12,L12,D12,L20,U20,L21,D21,U21,L22,D22];
I = ideal (U00*R01-R00*U10,R01*D11-D01*R00,D11*L10-L11*D01,L10*U00-U10*L11,U01*R02-R01*U11,R02*D12-D02*R01,D12*L11-L12*D02,L11*U01-U11*L12,U10*R11-R10*U20,R11*D21-D11*R10,D21*L20-L21*D11,L20*U10-U20*L21,U11*R12-R11*U21,R12*D22-D12*R11,D22*L21-L22*D12,L21*U11-U21*L22);
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
assert (intersect bpd == I); 

-- another 'random' example
R = QQ[a..h]
I = ideal(d*g*h-e*g*h,a*b*g-c*f*h,a*b*c-e*g*h,c*f*h^2-d*f,e^2*g*h-d*h,b*d*f*h-c*g,a*d*f*g-c*e,b*c*e*g-a*f,a*b*e*f-c*d);
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
assert (intersect bpd == I); 

-- The 2,1 Mayr-Meyer ideal
R = QQ[s, f, b01, b02, b03, b04, b11, b12, b13, b14, c01, c02, c03, c04, c11, c12, c13, c14]
I = ideal(-f*b01*c01+s*c01,-f*b02*c02+s*c02,-f*b03*c03+s*c03,-f*b04*c04+s*c04,f*c01-s*c02,-s*c03+f*c04,-s*c02+s*c03,
     f*b01*c02-f*b04*c03,-f*b03*b11*c02*c11+f*b02*c02*c11,-f*b03*b12*c02*c12+f*b02*c02*c12,-f*b03*b13*c02*c13+f*b02*c02*c13,
     -f*b03*b14*c02*c14+f*b02*c02*c14,s*c04*c11-s*c01*c12,-s*c01*c13+s*c04*c14,-s*c01*c12+s*c01*c13,
     s*b11*c04*c12-s*b14*c04*c13,s*b12*c04*c12-s*b13*c04*c12)
time bpd = binomialPrimaryDecomposition (I,verbose=>false);
assert (intersect bpd == I); 

quit();


