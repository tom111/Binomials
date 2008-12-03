R = QQ['a,b,c,d,e']
(a,b,c,d,e) = R.gens()
I = R*(a^2 - 1, b^4 - b^2, c*b^2 - c, c^4 - c^3, d*c^3 - c^3*a, d^2*b^2 - d^2, e*c^3 - c^3*b, e^2*b^2 - e^2, e^2*d^6 - d^4, e^7*d^5 - e^5*d^3, e^8*d^4 - e^6*d^2, e^9*d^3 - e^7*d , e^10*d^2 - d^8)
primdec = I.primary_decomposition();

def conj_term(t1, t2):
    if t1.monomial_coefficient(a^0) == - t2.monomial_coefficient(a^0):
        return true
    else:
        return false

def fitting_generators (g1,g2):
    sdiff = set(g1).symmetric_difference(set(g2))
    if len(sdiff) == 2:
        s1 = sdiff.pop()
        s2 = sdiff.pop()
        if conj_term(s1,s2) :
            return true
    if len(sdiff) == 4:
        s1 = sdiff.pop()
        s2 = sdiff.pop()
        s3 = sdiff.pop()
        s4 = sdiff.pop()
        if conj_term(s1,s2) or conj_term(s1,s3) or conj_term(s1,s4): 
            return true
        if conj_term(s2,s3) or conj_term(s2,s4) or conj_term(s3,s4):
            return true
    return false

ol = 0
while(ol != len(primdec)):
    ol = len(primdec)
    # print(ol)
    running = true
    for I in primdec:
        if running:
            for J in primdec:
                if running:
                    if fitting_generators(I.reduced_basis(),J.reduced_basis()):
                        primdec.append(I.intersection(J))
                        primdec.remove(I)
                        primdec.remove(J)
                        running = false


output = [J.reduced_basis() for J in primdec]
output
