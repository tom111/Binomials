R = QQ[x1,x2,x3,x4,x5]
I = ideal( x1*x4^2 - x2*x5^2,  x1^3*x3^3 - x4^2*x2^4, x2*x4^8 - x3^3*x5^6)
-- Here is a cellular decomp  of I:
-- This is also a prime decomposition
J1 = ideal({x1^2 , x1*x4^2 - x2*x5^2, x2^5, x5^6, x2^4 * x4^2,x4^8})
J2 = ideal({x1*x4^2 - x2*x5^2, x1^3*x3^3 - x4^2*x2^4, x2^3*x4^4 - x1^2*x3^3*x5^2, x2^2*x4^6 - x1*x3^3*x5^4, x2*x4^8 - x3^3 *x5^6 })


Q = QQ[x,y,z]
J = ideal(x^4*y^2-z^6,x^3*y^2-z^5,x^2-y*z)
-- The cellular decomposition is also a primary decomposition.
-- No lattice needs to be saturated, only roots of monomials

Q = QQ[x,y,z,w]
J = ideal(x^4*w^2-z^6,x^3*y^2-z^5,x^7-y^3*w^2,x^2*x^3-z^7)

axisSaturate = (I,i) -> (
-- By Ignacio Ojeda and Mike Stillman
-- For computing saturations w.r.t. a single variable:
    R := ring I;
    I1 := ideal(1_R);
    s = 0;
    f = R_i;
    while not(I1 == I) do (
	s = s + 1;
	I1 = I;
	I = ideal syz gb(matrix{{f}}|gens I,
            SyzygyRows=>1,Syzygies=>true););
    {s-1, I}
    )

-- Cellular decomposition of binomial ideals:
--

binomialCD = (I) -> (
-- By Ignacio Ojeda and Mike Stillman     
     R := ring I;
     n := numgens R;
     Answer = {};
     IntersectAnswer = ideal(1_R);
     ToDo = {{1_R,toList(0..n-1),I}};
     compo = 0;
     next = () -> (
	 if #ToDo === 0 then false
	 else (
	      L = ToDo#0;
	      ToDo = drop(ToDo,1);
	      if gens IntersectAnswer % L#2 == 0
	      then (<< "redundant component" << endl;)
	      else if #(L#1) === 0 then (
		   -- We have an answer
                   compo = compo + 1; 
		   newone := trim L#2;
		   << "component: " << {compo, gens newone} << endl;
		   Answer = append(Answer,newone);
		   IntersectAnswer = intersect(IntersectAnswer,newone);
		   if IntersectAnswer == I then ToDo = {})
	      else (
	           i := L#1#0;
		   newL1 = drop(L#1,1);
	           result = axisSaturate(L#2, i);
		   J := result#1;
		   k := result#0;
		   if k > 0 then (
			J2 = L#2 + ideal(R_i^k);
			-- We need to remove any components supported on the first vars
			J2 = saturate(J2, L#0);
			if J2 != ideal(1_R) then
			    ToDo = prepend({L#0, newL1, J2},ToDo));
		   if J != ideal(1_R) then ToDo = prepend({R_i * L#0, newL1, J},ToDo);
		   );
	      true));
     while next() do ();
     Answer	      
     )

-- This function saturates an integer lattice. It expects 
-- the matrix A, whose image is the lattice. 
Lsat = (A) -> gens ker transpose gens ker transpose A;

partialCharacter = (I) -> (
     vs := {}; -- This will hold the lattice generators
     cl := {}; -- This will hold the coefficients
     R := ring I;
          
     -- The input should be a cellular ideal 
     cellvars := cellVars(I);
     
     -- We intersect I with the ring k[E]
     -- In many cases this will be zero
     CoeffR := coefficientRing R;
     S := CoeffR[cellvars];
     II := kernel map (R/I,S);

     -- The partial Character of the zero ideal is the 
     -- zero lattice.       
     if ( II == 0 ) then (
	  for i in gens ring II do vs = vs | { 0 };
	  cl = {1};
	  return (cellvars, transpose matrix {vs}, cl);
	  );
     
     -- So, II is not zero:
     -- Let ts be the list of generators
     ts := entries gens II;
     -- for each term, find the exponent vector
     for t in ts#0 do (
-- 	  if t != 0 then ( -- Term is nonzero already
          vs = vs | {((exponents (t))#0 - (exponents (t))#1)};
          coeffs := entries ((coefficients(t))#1);
          -- I hope that coefficients returns the leading coeff as 0th
          cl = cl | { -coeffs#1#0 / coeffs#0#0}
--          );
	  );
--    print coeffs;
--    print cl;
     
     -- back to the old ring
     use R;
     return (cellvars, transpose matrix vs , cl);
     )

cellVars = (I) -> (
     cv = {};
     for i in gens ring I do if saturate (I,i) != substitute(ideal(1), ring I) then cv=cv|{i};
     return cv;
     )

nonCellstdm = (I) -> (
     R := ring I;
     cv := set(cellVars(I)); 
     -- Here go the non-cell variables
     ncv := toList(set (gens R) - cv);
     -- We project I to the non-cell variables
     Q := QQ[ncv];
     projnE := map (Q,R);
     J := projnE I;
     S = Q/J;
     slist = entries flatten basis (S);
     use R;
     return slist;
     )
  
satpchar = ( A , c) -> (
     
     -- print A;
     -- print c;
     
     sageprogfile = temporaryFileName() | ".sage";
     sageoutfile = temporaryFileName();
     -- We paste the whole program in:
     F = openOut(sageprogfile);
     
-- Oh my god, this is impossible to debug :(
F << "def rectsolve (A,S): " << endl;
F << "    cl = A.columns()" << endl;
F << "    krows = len(S.columns())" << endl;
F << "    kcols = len(A.columns())" << endl;
F << "    varnames = []" << endl;
F << "    for i in range(krows) :" << endl;
F << "        for j in range(kcols) :" << endl;
F << "            # print [i,j]" << endl;
F << "            varnames = varnames + ['k'+str(i)+str(j)]" << endl;
F << "    for v in varnames:" << endl;
F << "        var(v)" << endl;
F << "    i = 0" << endl;
F << "    vs = []" << endl;
F << "    K = matrix(krows,kcols)" << endl;
F << "    for a in cl:" << endl;
F << "        vs = []" << endl;
F << "        for j in range(krows):" << endl;
F << "            vs = vs + ['k'+str(j)+str(i)]" << endl;
F << "        vs2 = [eval(v) for v in vs]" << endl;
F << "        # print vs" << endl;
F << "        eqns = S * vector(vs2) - a" << endl;
F << "        s = solve ( list(eqns) , tuple(vs2), solution_dict=True)" << endl;
F << "        for j in range (krows):" << endl;
F << "            K[j,i] = (s[0])['k'+str(j)+str(i)]" << endl;
F << "        i = i +1" << endl;
F << "    return K;" << endl;
F << "def Lsat(A):" << endl;
F << "    ker = kernel(A)" << endl;
F << "    kerb = matrix(ZZ,transpose(ker.basis_matrix()))" << endl;
F << "    return transpose(kernel(kerb).basis_matrix())" << endl;
F << "def charsat (A,l) :" << endl;
F << "    S = Lsat(A)" << endl;
F << "    K = rectsolve(A,S)" << endl;
F << "    varnames = []" << endl;
F << "    rg = len(S.columns())" << endl;
F << "    for i in range(rg) :" << endl;
F << "        varnames = varnames + ['m'+str(i)]" << endl;
F << "    for v in varnames:" << endl;
F << "        # print v" << endl;
F << "        var (v)" << endl;
F << "    eqns = []" << endl;
F << "    kr = len(K.rows())" << endl;
F << "    kc = len(K.columns());" << endl;
F << "    for col in range(kc):" << endl;
F << "        monom = 1" << endl;
F << "        for row in range(kr):" << endl;
F << "            monom *= eval('m'+str(row))^K[row,col]" << endl;
F << "            # print eval('m'+str(row))^K[row,col]" << endl;
F << "        eqns = eqns + [ monom - l[col] ]" << endl;
F << "    satlist = [] # The list of saturations" << endl;
F << "    vs = [eval(v) for v in varnames]" << endl;
F << "    if (len (eqns) > 1) :" << endl;
F << "        s = solve (eqns , tuple(vs), solution_dict=True)" << endl;
F << "    else :" << endl;
F << "        spre = solve (eqns , tuple(vs))" << endl;
F << "        # print spre" << endl;
F << "        s= [dict([(eq.left(),eq.right())]) for eq in spre ]" << endl;
F << "    m = [] " << endl;
F << "    for sol in s :" << endl;
F << "        n = [] " << endl;
F << "        for v in varnames:" << endl;
F << "            n = n + [sol[v]]" << endl;
F << "        m = m + [n]" << endl;
F << "    return (S,m)" << endl;

F << "A = matrix(ZZ,[";

-- Here goes the lattice defining matrix
ent = entries A;
for r in (0..(#ent -1)) do (
     F << "[";
     for c in (0..(#(ent#r)-1)) do (
	  F << ent#r#c;
	  if (c < (numcols A) -1 ) then F << ",";
	  );
     F << "]";
     if (r < (numrows A) -1) then F << ",";
     );
F << "])" << endl;

-- Here goes the character
F << "c = [";
for i in (0..((#c)-1)) do (
     F << c#i ;
     if (i< (#c -1)) then F << ",";
     );
F << "]" << endl;

-- Here we do output
F << "res = charsat(A,c)" << endl;
F << "M2mat = 'S = matrix {';" << endl;
F << "nr = len (res[0].rows())" << endl;
F << "nc = len (res[0].columns())" << endl;
F << "for r in range(nr):" << endl;
F << "    M2mat = M2mat + '{'" << endl;
F << "    for c in range (nc):" << endl;
F << "        M2mat = M2mat+ str((res[0])[r][c]);" << endl;
F << "        if (c < (nc-1)): " << endl;
F << "            M2mat = M2mat + ',';" << endl;
F << "    M2mat = M2mat + '}';" << endl;
F << "    if (r < nr-1) :" << endl;
F << "        M2mat = M2mat + ',';" << endl;
F << "M2mat = M2mat + '}';" << endl;
F << "print M2mat;" << endl;
F << "charstr = str(res[1]).replace('I','ii');" << endl;
F << "charstr = charstr.replace('[','{');" << endl;
F << "charstr = charstr.replace(']','}');" << endl;
F << "print 'c = ' + charstr" << endl;

     close (F);
     
     execstr = "sage "|sageprogfile | " > " | sageoutfile ;
     -- print execstr;
     ret := run (execstr);
     if (ret != 0) then (
	  print "sage did not run correctly, sorry :(";
	  return False;
	  );
     
     outlines = lines get sageoutfile;
     
     S := value outlines#0;
     cl := value outlines#1;
     return (S,cl)
     )

BinassPrim = (I) -> (
     R := ring I;
     ml := nonCellstdm(I);
     cv := cellVars(I);
     ncv := toList(set (gens R) - cv);
     Q := QQ[cv];
     use R;
     for m in ml do (
	  print " "
	  )
     )   
     