-- -*- coding: utf-8 -*-
--  cyclotomic.m2
--
--  Copyright (C) 2009 Thomas Kahle <kahle@mis.mpg.de>
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or (at
--  your option) any later version.
--
--  This program is distributed in the hope that it will be useful, but
--  WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
--  General Public License for more details.
--
--  You should have received a copy of the GNU General Public License along
--  with this program; if not, write to the Free Software Foundation, Inc.,
--  59 Temple Place, Suite 330, Boston, MA 02111-1307 USA.
--
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

newPackage(
	"cyclotomic",
    	Version => "0.2", 
    	Date => "May 2009",
    	Authors => {{Name => "Thomas Kahle", 
		  Email => "kahle@mis.mpg.de", 
		  HomePage => "http://personal-homepages.mis.mpg.de/kahle/"}},
    	Headline => "routines for cyclotomic fields",
    	DebuggingMode => true
    	)

export {cyclotomicField,
        cyclotomicPoly,
	FindRootPower
       }

cyclotomicField = (i,R) -> (
     -- Given a ring R, and a power i, the cyclotomic field is returned
     return toField (R / sub (ideal(cyclotomicPoly (i,R_0)) ,R));
     )

-- Inverting Roots manually
-- cycloInverse = ()    

cyclotomicPoly = (i,v) -> (
     -- returns the i-th cyclotomic polynomial in variable v.
     -- v must be a variable a priori
     v = value v;
     if i <= 0 then error "the input should be > 0.";
     if i==1 then return v-1 ;
     min := v^i -1;
     -- dividing out the first cylcotomic polynomial
     -- (with result a polynomial)
     min = (flatten entries syz matrix {{min ,(v-1)}})#1; 

     -- i is prime:
     if isPrime i then return min / (leadCoefficient min);
     
     -- i is not prime:
     -- find the divisors:
     for f in toList (2..i//2) do (
	  -- check for factor
	  if i%f == 0 then (
	       fac := cyclotomicPoly (f,v);
	       -- print fac;
	       -- division with result in polynomial ring:
	       min = (flatten entries syz matrix {{min,fac}})#1;
	       )
	  );
     --make sure the leading coefficient is one.
     min=min / leadCoefficient(min);            
     return(min);                        
)

FindRootPower = R -> (
     -- Finds the power of the adjoined root of unity in the
     -- coefficient ring of R by just exponentiating.
     -- Returns '2' if the input was a polynomial ring over QQ
     r := 0;
     F := coefficientRing R;
     g := gens F;
     if #g == 0 then return 2;
     if #g > 1 then error "The coefficient field has more than one generator";
     g = value (g#0);
     gg := g; -- the generator
     while not 1_F == gg do (
	  r = r+1;
	  gg = gg *g;
	  );
     if r<2 then return 2
     else return r+1;
     )