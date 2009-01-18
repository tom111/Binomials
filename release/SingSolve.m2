--  SingSolve.m2
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
	"SingSolve",
    	Version => "0.1.1", 
    	Date => "January 8 , 2009",
    	Authors => {
	     {Name => "Thomas Kahle", Email => "kahle@mis.mpg.de", HomePage => "http://personal-homepages.mis.mpg.de/kahle/"}},
    	Headline => "Interface to Singulars solve facility",
	Configuration => { "path" => "Singular"	},
    	DebuggingMode => true
    	)

export {singsolve}

path'singular = (options SingSolve).Configuration#"path"
-- NOTE: the absolute path should be put into the .init file for 4ti2 inside the .Macaulay2 directory.

-- the following command is necessary to be run under windows-cygwin:
-- externalPath = value Core#"private dictionary"#"externalPath"
-- Note: outside of cygwin (linux/mac), this string is just the null string. 
-- But under Windows machines this is necessary (the value of the string is C:/cygwin).
-- externalPath = replace("\\\\","/",value Core#"private dictionary"#"externalPath")
-- Without this command, the temporary files won't be found and there will be a ton of error messages.

singsolve = method(TypicalValue => List)
singsolve Ideal := List => I -> (
     -- This function numerically solves a 0-dim'l ideal using singular
     if dim I != 0 then error "Expected 0-dim'l ideal !";
     
     print Configuration;
     -- We coerce the ideal to singular
     F := openInOut ("!" | path'singular);
     
     varlist := gens ring I;
     -- We create the ring:
     F << "ring R = 0,(";
     F << concatenate (between_"," varlist/toString);
     F << "),dp;" << endl;
     F << "ideal I = ";

     ge = flatten entries gens I;
     -- We convert the generators to a string representation
     F << concatenate(between_"," ge/toString, ";");

     -- Lets solve the ideal
     F <<"LIB \"solve.lib\"; ";
     F <<"def S = solve(I);" << endl;
     F <<"setring S;" << endl;
     F <<"print (SOL,\"%s\");" << endl;
     F << endl;
     F << "quit;";
     -- Done with programming
     F << closeOut; 
     

     print "Running Singular";
     outlines := lines get F;
     
     -- Second to last line contains the result
     -- Singular uses "i" as the complex unit.
     cl :=  toList value replace("i","ii",outlines#-2);
     -- cl now contains a flat list of values like 
     -- x_0,y_0,z_0,x_1,y_1,z_1, ..
     -- print cl;
     
     numvars := #varlist;  -- Number of variables should divide length of cl.
     numsols := #cl // numvars; -- ... and give number of solutions
     print ("Number of solutions: " | numsols);
     
     return  pack (numvars, cl);
     
     )

endPackage "SingSolve"
