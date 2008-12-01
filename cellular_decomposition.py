def cellular_decomposition (I):
    """
    This function computes the cellular decomposition of a binomial ideal
    
    OUTPUT: A list of cellular ideals whose intersection is the input
    """

    if is_cellular(I):
        return [I]
    else:
        badvar = is_cellular(I)
        print(badvar)

    """ We can do the variable saturation by hand """
    def varsat (I, var):
        """
        Computes the saturation of an ideal I with respect to 
        variable 'var' 
        """
        I2 = 0 * R
        l = 0
        while I2 != I:
            l = l+1
            I2 = I
            I = I.quotient(var * R)
        return [I,l]
    # End of varsat function
        
    [J,l] = varsat(I,badvar)
    K = I + (badvar^l)*R
    
    
