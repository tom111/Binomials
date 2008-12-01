def saturate (A):
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

