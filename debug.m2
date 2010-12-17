-- restart

R = QQ[x,y,z]
I = ideal(x^2, x*y, y^2, x*(z^3-1), y*(z^2-1))
bpd = BPD I
intersect bpd == sub (I, ring bpd#0)

I = ideal(x^2- x*y, x*y- y^2, x*(z^3-1), y*(z^2-1))
bpd = BPD I
intersect bpd == sub (I, ring bpd#0)


-- Lsat improvement
 --R = QQ[a..h]
 --M = matrix {{2,0,-1,0,0}, { -1, 1,  -2, -1, 0 }, { -1, 2,  2,  -1, -2}, {0 , 0,  2,  0,  0 }, { 0,  0,  0,  1,  2 }, 
 --     { 0,  1,  0,  2,  0}, { 0,  -1, 0,  0,  2}, { 0,  0,  0,  2,  2}  }
 ---- is this a bug?
 --Lsat = A -> LLL syz transpose LLL syz transpose A;
 --image LLL syz transpose M == image syz transpose M
 --Lsat M
 --isSubset (image M ,image Lsat M)
 --
-- -- Original stuff:
-- S = QQ[R00,U00,R01,D01,U01,R02,D02,R10,L10,U10,R11,L11,D11,U11,R12,L12,D12,L20,U20,L21,D21,U21,L22,D22];
-- I = ideal (U00*R01-R00*U10,R01*D11-D01*R00,D11*L10-L11*D01,L10*U00-U10*L11,U01*R02-R01*U11,R02*D12-D02*R01,D12*L11-L12*D02,L11*U01-U11*L12,U10*R11-R10*U20,R11*D21-D11*R10,D21*L20-L21*D11,L20*U10-U20*L21,U11*R12-R11*U21,R12*D22-D12*R11,D22*L21-L22*D12,L21*U11-U21*L22);
-- 
-- -- Debugging binomial quotients:
-- I1 = ideal(U21,D21,L12,U11,D11,L11,U01,U00,R00,D22^2,D12*D22,R01*D22,D12*L22-L21*D22,U20^2,U10*U20,U10*L20-U20*L21,D12^2,R11*D12-R12*D22,R01*D12,U10*R11-R10*U20,U10^2,R01*D02-R02*D12,R01^2,R01*R11*L21-R01*R12*L22,R10*L20-R11*L21)                          
-- b1 = R11*L21-R12*L22                                                                                                              
-- I2 = ideal(U21,D21,L12,U11,D11,L11,U01,U00,R00,D22^2,D12*D22,R01*D22,D12*L22-L21*D22,U20^2,U10*U20,U10*L20-U20*L21,D12^2,R11*D12-R12*D22,R01*D12,U10*R11-R10*U20,U10^2,R01*D02-R02*D12,R01^2,R01*R11*L21-R01*R12*L22)                                          
-- b2 = R11*L21-R12*L22                                                                                                              
-- I3 = ideal(D22,U21,D21,D12,L12,U11,D11,L11,U01,R01,U00,R00,U20^2,U10*U20,U10*L20-U20*L21,U10*R11-R10*U20,U10^2)                   
-- b3 = R10*L20-R11*L21                                                                                                              
-- I4 = ideal(U21,D21,L12,U11,D11,L11,U01,U00,R00,D22^2,D12*D22,R01*D22,D12*L22-L21*D22,U20^2,U10*U20,U10*L20-U20*L21,D12^2,R11*D12-R12*D22,R01*D12,U10*R11-R10*U20,U10^2,R01*D02-R02*D12,R01^2,R01*R11*L21-R01*R12*L22,R11*L21-R12*L22)                          
-- b4 = R10*L20-R12*L22
-- 
-- debug Binomials
-- isBinomial (I1:b1)
-- load "Binomials.m2"
-- debug Binomials
-- time binomialQuotient (I2, b2)
-- time I2:b2
-- binomialQuotient (I4, b4) == (I4:b4)
-- 
-- load "Cyclotomic.m2"
-- 
-- F = cyclotomicField (3)
-- G = cyclotomicField (4)
-- 
-- R = F[x]
-- S = G[x]
-- 
-- use R
-- ww = (gens F)#0
-- I = ideal (x-ww)
-- use S 
-- ww = (gens G)#0
-- J = ideal (x-ww)
-- 
-- print joinCyclotomic ({I,J})
-- 
-- 
-- restart
-- load "Binomials.m2"
-- R = QQ[x,y,z]
-- I = ideal(x^2-y,y^2-z^2,z^2-x)
-- dim I
-- degree I
-- bpd = BPD I; toString bpd
-- mingens intersect bpd 
-- intersect bpd == sub (I, ring bpd#0)
-- 
-- I1 = intersect (bpd#0,bpd#1)
-- I2 = intersect (I1,bpd#2)
-- I3 = intersect (I2,bpd#3)

-- mingens I3

-- K is contained in I as can be seen by means of primary decomposition
-- mpI = binomialMinimalPrimes I
-- mpJ = binomialMinimalPrimes J
-- 
-- -- now confirm that the first three minprimes of I are actually all the minprimes of J
-- -- mathematically everything lives in the same ring:
-- S = ring mpJ#0
-- print S
-- 
-- I0 = sub(mpI#0,S)
-- I1 = sub(mpI#1,S)
-- I2 = sub(mpI#2,S)
-- 
-- print (sub(mpI#0, S) == mpJ#0)
-- print (sub(mpI#1, S) == mpJ#1)
-- print (sub(mpI#2, S) == mpJ#2)
-- 
-- print (I0 == mpJ#0)
-- print (I1 == mpJ#1)
-- print (I2 == mpJ#2)
-- 
-- print (sub( intersect {mpI#0,mpI#1,mpI#2} , S) == intersect {mpJ#0,mpJ#1,mpJ#2} )
-- print (intersect {I0,I1,I2} == intersect {mpJ#0,mpJ#1,mpJ#2} )
-- 

