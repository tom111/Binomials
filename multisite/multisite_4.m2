R=QQ[	s0000, i0000, 
	s0001, i0001, j0001, 
	s0010, i0010, j0010, 
	s0011, i0011, j0011, 
	s0100, i0100, j0100, 
	s0101, i0101, j0101, 
	s0110, i0110, j0110, 
	s0111, i0111, j0111, 
	s1000, i1000, j1000, 
	s1001, i1001, j1001, 
	s1010, i1010, j1010, 
	s1011, i1011, j1011, 
	s1100, i1100, j1100, 
	s1101, i1101, j1101, 
	s1110, i1110, j1110, 
	s1111, j1111, 
	e, f];
reactionsIdeal=ideal(	e*s0000-i0000, i0000*(s0000-e*s1000),
	f*s1000-j1000, j1000*(s1000-f*s0000),
	e*s0000-i0000, i0000*(s0000-e*s0100),
	f*s0100-j0100, j0100*(s0100-f*s0000),
	e*s0000-i0000, i0000*(s0000-e*s0010),
	f*s0010-j0010, j0010*(s0010-f*s0000),
	e*s0000-i0000, i0000*(s0000-e*s0001),
	f*s0001-j0001, j0001*(s0001-f*s0000),
	e*s0001-i0001, i0001*(s0001-e*s1001),
	f*s1001-j1001, j1001*(s1001-f*s0001),
	e*s0001-i0001, i0001*(s0001-e*s0101),
	f*s0101-j0101, j0101*(s0101-f*s0001),
	e*s0001-i0001, i0001*(s0001-e*s0011),
	f*s0011-j0011, j0011*(s0011-f*s0001),
	e*s0010-i0010, i0010*(s0010-e*s1010),
	f*s1010-j1010, j1010*(s1010-f*s0010),
	e*s0010-i0010, i0010*(s0010-e*s0110),
	f*s0110-j0110, j0110*(s0110-f*s0010),
	e*s0010-i0010, i0010*(s0010-e*s0011),
	f*s0011-j0011, j0011*(s0011-f*s0010),
	e*s0011-i0011, i0011*(s0011-e*s1011),
	f*s1011-j1011, j1011*(s1011-f*s0011),
	e*s0011-i0011, i0011*(s0011-e*s0111),
	f*s0111-j0111, j0111*(s0111-f*s0011),
	e*s0100-i0100, i0100*(s0100-e*s1100),
	f*s1100-j1100, j1100*(s1100-f*s0100),
	e*s0100-i0100, i0100*(s0100-e*s0110),
	f*s0110-j0110, j0110*(s0110-f*s0100),
	e*s0100-i0100, i0100*(s0100-e*s0101),
	f*s0101-j0101, j0101*(s0101-f*s0100),
	e*s0101-i0101, i0101*(s0101-e*s1101),
	f*s1101-j1101, j1101*(s1101-f*s0101),
	e*s0101-i0101, i0101*(s0101-e*s0111),
	f*s0111-j0111, j0111*(s0111-f*s0101),
	e*s0110-i0110, i0110*(s0110-e*s1110),
	f*s1110-j1110, j1110*(s1110-f*s0110),
	e*s0110-i0110, i0110*(s0110-e*s0111),
	f*s0111-j0111, j0111*(s0111-f*s0110),
	e*s0111-i0111, i0111*(s0111-e*s1111),
	f*s1111-j1111, j1111*(s1111-f*s0111),
	e*s1000-i1000, i1000*(s1000-e*s1100),
	f*s1100-j1100, j1100*(s1100-f*s1000),
	e*s1000-i1000, i1000*(s1000-e*s1010),
	f*s1010-j1010, j1010*(s1010-f*s1000),
	e*s1000-i1000, i1000*(s1000-e*s1001),
	f*s1001-j1001, j1001*(s1001-f*s1000),
	e*s1001-i1001, i1001*(s1001-e*s1101),
	f*s1101-j1101, j1101*(s1101-f*s1001),
	e*s1001-i1001, i1001*(s1001-e*s1011),
	f*s1011-j1011, j1011*(s1011-f*s1001),
	e*s1010-i1010, i1010*(s1010-e*s1110),
	f*s1110-j1110, j1110*(s1110-f*s1010),
	e*s1010-i1010, i1010*(s1010-e*s1011),
	f*s1011-j1011, j1011*(s1011-f*s1010),
	e*s1011-i1011, i1011*(s1011-e*s1111),
	f*s1111-j1111, j1111*(s1111-f*s1011),
	e*s1100-i1100, i1100*(s1100-e*s1110),
	f*s1110-j1110, j1110*(s1110-f*s1100),
	e*s1100-i1100, i1100*(s1100-e*s1101),
	f*s1101-j1101, j1101*(s1101-f*s1100),
	e*s1101-i1101, i1101*(s1101-e*s1111),
	f*s1111-j1111, j1111*(s1111-f*s1101),
	e*s1110-i1110, i1110*(s1110-e*s1111),
	f*s1111-j1111, j1111*(s1111-f*s1110) );
-- Try to decompose! 
time cd = binomialCD (reactionsIdeal + ideal(e)); 
time cd = binomialCD (reactionsIdeal + ideal(s0000); 
time cd = binomialCD (reactionsIdeal + ideal(s1000); 
time cd = binomialCD (reactionsIdeal + ideal(s1100); 
