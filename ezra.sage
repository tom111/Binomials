R = QQ['a,b,c,d,e']
(a,b,c,d,e) = R.gens()
I = R*(a^2 - 1, b^4 - b^2, c*b^2 - c, c^4 - c^3, d*c^3 - c^3*a, d^2*b^2 - d^2, e*c^3 - c^3*b, e^2*b^2 - e^2, e^2*d^6 - d^4, e^7*d^5 - e^5*d^3, e^8*d^4 - e^6*d^2, e^9*d^3 - e^7*d , e^10*d^2 - d^8)
primdec = I.primary_decomposition()
