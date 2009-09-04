R = QQ[a..x]
for i in 0..10 do (
     I = randomBinomialIdeal (R,10,1,4,true);
     << toString I << endl;
     time bpd = BPD I;
     assert (intersect bpd == sub(I,ring bpd#0) );
     )
     