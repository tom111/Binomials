def is_cellular (I):
    """
    This function test whether a given binomial ideal is cellular.  In
    the affirmative case it output the largest subset of variables
    such that I is cellular.  In the negative case a variable which is
    a zerodivisor but not nilpotent is found.

    EXAMPLE
    R = QQ['a,b,c,d']
    (a,b,c,d) = R.gens()

    ALGORITHM: A1 in CS[00]

    TODOLIST:
    - Optimize the singular interaction 
    """

    R = I.ring()
    if I == I.ring():
        print("The ideal is the whole ring and not cellular")
        return false
    
    ring_variables = list(R.gens())

    """ We can do the variable saturation by hand """
    def varsat (I, var):
        """
        Computes the saturation of an ideal I with respect to 
        variable 'var' 
        """
        I2 = 0 * R
        while I2 != I:
           I2 = I
           I = I.quotient(var * R)
        return I
    # End of varsat function

    bad_variables = []
    
    for x in ring_variables:
       if varsat(I,x) == R :
           bad_variables = bad_variables + [x]

    # Use a list comprehension here !
    good_variables = ring_variables
    for x in bad_variables:
        good_variables.remove(x)

    print ("Here are the good variables:")
    print (good_variables)

    J = I
    for x in good_variables:
       J = varsat(J,x)
       
    print ("This is the full saturation with respect to the good variables")
    print (str(J))

    if I == J:
       print ("The ideal is cellular with respect to the good variables:")
       print (good_variables)
       return true
    else:
        for x in good_variables:
           if I != varsat(J,x):
              print ('The variable ', x, ' is a zerodvisior but not nilpotent.' )
              return false
            
          
 
