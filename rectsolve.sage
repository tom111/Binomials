def rectsolve (A,S):
    r""" Let A,S be matrices with suitable dimensions.
    This function returns a matrix K such that 
    A = S . K
    """
    cl = A.columns()
    krows = len(S.columns())
    kcols = len(A.columns())

    varnames = []
    for i in range(krows) :
        for j in range(kcols) :
            # print [i,j]
            varnames = varnames + ['k'+str(i)+str(j)]
    
    """ Varnames are filled now 
    We fill the k-matrix with the apropriate values 
    """

    """ Declare them to be variables"""
    for v in varnames:
        var(v)

    i = 0
    vs = []
    """ Here we will save the solution """
    K = matrix(krows,kcols)
    for a in cl:
        vs = []
        for j in range(krows):
            vs = vs + ['k'+str(j)+str(i)]
        """ Variable list (a column of K)  is ready !"""
        vs2 = [eval(v) for v in vs]
        # print vs
        eqns = S * vector(vs2) - a
        s = solve ( list(eqns) , tuple(vs2), solution_dict=True)
        """ This returns a list of solution dictionaries !"""
        if len(s) > 1 :
            print "WARNING: MORE THAN ONE SOLUTION!"
        for j in range (krows):
            K[j,i] = (s[0])['k'+str(j)+str(i)]
        i = i +1

    return K;

def Lsat(A):
    """Compute the saturation of an integer lattice 
    The generators of the lattice are the columns of the 
    input matrix 

    EXAMPLE
    L = matrix(ZZ,[[2],[2],[2]])
    saturate(L)

    TODOLIST:
    - Check if we can shortcut to Z^d (full rank)
    - What is the correct output format (ZZ - Module / or Matrix ?)
    """

    ker = kernel(A)
    kerb = matrix(ZZ,transpose(ker.basis_matrix()))

    """ This statement would return the module :
    return kernel(kerb)
    """

    """ This returns a matrix """
    return transpose(kernel(kerb).basis_matrix())

def charsat (A,l) :
    r""" Computes the possible saturations of a partial character, the
    input should be a matrix having the lattice as their image and the
    corresponding values of the character on the generators
    """
    S = Lsat(A)
    
    K = rectsolve(A,S)
    # We construct the binomial equations that have the 
    # saturated character as their solution

    varnames = []
    rg = len(S.columns())
    for i in range(rg) :
        varnames = varnames + ['m'+str(i)]
    
    for v in varnames:
        print v
        var (v)

    eqns = []
    kr = len(K.rows())
    kc = len(K.columns());
    for col in range(kc):
        monom = 1
        for row in range(kr):
            monom *= eval('m'+str(row))^K[row,col]
            print eval('m'+str(row))^K[row,col]
        eqns = eqns + [ monom - l[col] ]

    satlist = [] # The list of saturations
    print eqns
    vs = [eval(v) for v in varnames]
    # This is a hack since solution dict is broken for univariate 
    # equations.
    if (len (vs) > 1) :
        s = solve (eqns , tuple(vs), solution_dict=True)
    else :
        spre = solve (eqns , tuple(vs))
        print spre
        s= [dict([[eq.left(),eq.right()] for eq in spre ])
        
    m = []
    print s
    for v in varnames :
        m = m + s[v]
