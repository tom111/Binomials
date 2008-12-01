"""
private data: 

New:

__complete_cellular_decomposition - A list
containing binomial cellular ideals whose intersection is the given
ideal

__not_nilpotent_zerodivisors - a list of variables which are
zerodivisors while not nilpotent. Useful during the computation of a
cellular decomposition

__cell_variables - Save the maximal set delta of variables with
respect to which it is cellular(AS A LIST!). If delta is empty the
ideal is not cellular

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
        self.__not_nilpotent_zerodivisors = []
        self.__cel_variables = []

    def varsat (self, I, var):
        """
        Computes the saturation of an ideal with respect to 
        variable 'var' and returns also the necessary exponent
        """
        I2 = 0 * R
        l = 0 
        while I2 != I:
           I2 = I
           l = l+1
           I = I.quotient(var * R)
        return (I,l-1)
    # End of varsat function

    def is_cellular (self):
        r""" This function test whether a the ideal is cellular.  In
        the affirmative case it saves the largest subset of variables
        such that I is cellular.  In the negative case a variable
        which is a zerodivisor but not nilpotent is found.

        EXAMPLE 
        
        ALGORITHM: A1 in CS[00]

        TODOLIST:
        - Optimize 
        """

        # Check if we did the computation already instead of setting it to zero!
        self.__not_nilpotent_zerodivisors = []

        R = self.ring()
        if I == 1*R:
            # print("The ideal is the whole ring and not cellular")
            return false

        ring_variables = list(R.gens())

        bad_variables = []

        for x in ring_variables:
            if self.varsat(self, x)[0] == 1*R :
                bad_variables = bad_variables + [x]

        # We should use a list comprehension here !
        self.__cell_variables = ring_variables
        for x in bad_variables:
            self.__cell_variables.remove(x)

        print ("Here are the cell variables:")
        print (self.__cell_variables)

        varprod = 1
        for x in self.__cell_variables:
            varprod = varprod * x
        print(varprod)
        J = self.varsat(self, varprod)[0]

        print ("This is the full saturation with respect to the good variables")
        print (str(J))

        if self == J:
           print ("The ideal is cellular with respect to the cell variables:")
           print (self.__cell_variables)
           return true
        else:
            for x in self.__cell_variables:
                if self != self.quotient(x*R):
                    print ('The variable',x,' is a zerodvisior but not nilpotent.' )
                    self.__not_nilpotent_zerodivisors += [x]

            print (self.__not_nilpotent_zerodivisors)
            return false           


    def cellular_decomposition(self):
        r""" 
        Returns a list of cellular ideals such that their
        intersection is $I$ = \code{self}.

        EXAMPLES:
        sage: R = QQ['x1,x2,x3,x4,x5']
        sage: (x1,x2,x3,x4,x5) = R.gens()
        

        ALGORITHM: ???
        
        REFERENCES: ??? 
        """
        
        try:
            return self.__complete_cellular_decomposition
        except AttributeError:
            self.__complete_cellular_decomposition = {}
        except KeyError:
            pass
        
        V = []
        # The computation starts here 
        if self.is_cellular():
            V = [I]
        else:
            badvar = self.__not_nilpotent_zerodivisors[0]
            # print(badvar)

            (J,l) = self.varsat(I,badvar)
            # print(J,l)
            # Start a recursion

            ## HERE IS A BUG IN THE CHOICE OF THE EXPONENT !!!


            print ("The variable and exponent are :")
            print (badvar, l)
            K = BinomialIdeal(self.ring(), list(self.gens()) + [badvar^l])
            M = BinomialIdeal(self.ring(), J.gens())
            if K != 1*K.ring():
                print (K)
                print ("is not the full ring -> recurse")
                V + K.cellular_decomposition()
            if M != 1* R:
                print (M)
                print ("is not the full ring -> recurse")
                V + M.cellular_decomposition()

        # Finished the true computation 

        self.__complete_cellular_decomposition = V
        return self.__complete_cellular_decomposition
    
    
"""
The Algorithm:
Starting from a binomial ideal
1) Compute a Cellular Decomposition
2) Compute primary decompositions of the cellular ideals
"""


