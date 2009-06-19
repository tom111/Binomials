restart
load "Cyclotomic.m2"

F = cyclotomicField (3)
G = cyclotomicField (4)

R = F[x]
S = G[x]

use R
ww = (gens F)#0
I = ideal (x-ww)
use S 
ww = (gens G)#0
J = ideal (x-ww)

print joinCyclotomic ({I,J})


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

