from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal

class BinomialIdeal(MPolynomialIdeal):
    def __init__(self, ring, gens, coerce=True):
        MPolynomialIdeal.__init__(self, ring, gens, coerce)
    

    

