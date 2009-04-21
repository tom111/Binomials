load "Binomials.m2";
R = QQ[a..x];
I33 = ideal(a*n-m*b, n*h-g*m, h*s-t*g, s*a-b*t,  d*o-n*e, o*k-j*n, k*t-u*j, t*d-e*u, b*q-p*c, q*i-h*p, i*v-w*h, v*b-c*w,  e*r-q*f, r*l-k*q, l*w-x*k, w*e-f*x);
time pd = BPD I33;
quit;

-- R = QQ[a..m];
-- I = ideal "a7bcd2-mg,b6d7-abchijklm,mjk-d3c4";
-- time primaryDecomposition I;