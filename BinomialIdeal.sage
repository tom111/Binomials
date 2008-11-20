"""
private data: 

New:

__complete_cellular_decomposition - A sequence
containing binomial cellular ideals whose intersection is the given
ideal

Inherited:

__complete_primary_decomposition - A sequence of primary binomial
ideals whose intersection is the given ideal

__dimension - Vector space dimension of the ring modulo the ideal

__gb_singular - Groebnerbasis in Singular format

__singular - Singular Representation of the Ideal?

"""

from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal

class BinomialIdeal(MPolynomialIdeal):
    def __init__(self, ring, gens, coerce=True):
        MPolynomialIdeal.__init__(self, ring, gens, coerce)

    def cellular_decomposition(self):
        r""" 
        Returns a list of cellular ideals such that their
        intersection is $I$ = \code{self}.

        EXAMPLES:

        ALGORITHM: ???
        
        REFERENCES: ??? 
        """
        
        try:
            return self.__complete_cellular_decomposition
        except AttributeError:
            self.__complete_cellular_decomposition = {}
        except KeyError:
            pass
        
        """ Insert Computation Here """
        V = 2

        self.__complete_cellular_decomposition = V
        return self.__complete_cellular_decomposition
    
    
"""
The Algorithm:
Starting from a binomial ideal
1) Compute a Cellular Decomposition
2) Compute primary decompositions of the cellular ideals
"""


