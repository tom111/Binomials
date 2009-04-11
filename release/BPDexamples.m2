load "Binomials.m2"
R = QQ[a..x]
I22 = ideal(a*n-m*b, n*h-g*m, h*s-t*g, s*a-b*t,  d*o-n*e, o*k-j*n, k*t-u*j, t*d-e*u, b*q-p*c, q*i-h*p, i*v-w*h, v*b-c*w,  e*r-q*f, r*l-k*q, l*w-x*k, w*e-f*x)
time pd = BPD I22;

-- Check the result
intersect pd == I22

-- I33 is radical
testPrime \ pd

--------------------------------------------
load "Binomials.m2"
R = QQ[B001, B011, B101, B111, D010, D011, D110, D111, F000, F010, F100, F110, L100,L101, L110, L111, R000, R001, R010, R011, U000, U001, U100, U101];
I111 = ideal(R000*U100-U000*R010, R001*U101-U001*R011, R010*D110-D010*R000, R011*D111-D011*R001, L100*U000-U100*L110, L101*U001-U101*L111, L110*D010-D110*L100, L111*D011-D111*L101, R000*F100-F000*R001, R001*B101-B001*R000, R010*F110-F010*R011,R011*B111-B011*R010, L100*F000-F100*L101, L101*B001-B101*L100, L110*F010-F110*L111, L111*B011-B111*L110, F000*U001-U000*F010, B001*U000-U001*B011, F010*D011-D010*F000, B011*D010-D011*B001, F100*U101-U100*F110, B101*U100-U101*B111, F110*D111-D110*F100, B111*D110-D111*B101);

time pd = BPD I111;

-- Check the result
intersect pd == I111

-- I111 is radical
testPrime \ pd
