#!/usr/bin/python 
# outputs Macaulay 2 Code for the ideal I_{mn}
# as defined in Evans/Sturmfels/Uhler 08

import sys

print "-- Macaulay 2 Code for the Commuting Birth and Death Ideal:"

# Catching arguments:
try:
    m = int(sys.argv[1])
    n = int(sys.argv[2])
except IndexError:
    print '-- Please give 2 integer arguments'
    m = 1;
    n = 1;

print ('-- m = %i ,n = %i ' % (m,n))

# Generating the variable list:
varlist = []
for i in range(m+1):
    for j in range (n+1):
        if i<m: varlist.append(''.join(["R",str(i),str(j)]))
        if i>0: varlist.append(''.join(["L",str(i),str(j)]))
        if j>0: varlist.append(''.join(["D",str(i),str(j)]))
        if j<n: varlist.append(''.join(["U",str(i),str(j)]))

# varlist = varlist.sort()

s = "S = QQ["
s += ",".join(varlist)
s += "];"
print s


# Generating the equations
eqlist = []
for i in range(m):
    for j in range (n):
        eqlist.append(''.join(["U",str(i),str(j),"*R",str(i),str(j+1),"-",\
                               "R",str(i),str(j),"*U",str(i+1),str(j)]))
        eqlist.append(''.join(["R",str(i),str(j+1),"*D",str(i+1),str(j+1),"-",\
                               "D",str(i),str(j+1),"*R",str(i),str(j)]))
        eqlist.append(''.join(["D",str(i+1),str(j+1),"*L",str(i+1),str(j),"-",\
                               "L",str(i+1),str(j+1),"*D",str(i),str(j+1)]))
        eqlist.append(''.join(["L",str(i+1),str(j),"*U",str(i),str(j),"-",\
                               "U",str(i+1),str(j),"*L",str(i+1),str(j+1)]))

       

s = 'I = ideal ('
s += ",".join(eqlist)
s += ");"

print s

