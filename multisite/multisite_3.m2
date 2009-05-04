load "Binomials.m2"
R=QQ[	s000, i000, 
	s001, i001, j001, 
	s010, i010, j010, 
	s011, i011, j011, 
	s100, i100, j100, 
	s101, i101, j101, 
	s110, i110, j110, 
	s111, j111, 
	e, f];
reactionsIdeal=ideal(	e*s000-i000, i000*(s000-e*s100),
	f*s100-j100, j100*(s100-f*s000),
	e*s000-i000, i000*(s000-e*s010),
	f*s010-j010, j010*(s010-f*s000),
	e*s000-i000, i000*(s000-e*s001),
	f*s001-j001, j001*(s001-f*s000),
	e*s001-i001, i001*(s001-e*s101),
	f*s101-j101, j101*(s101-f*s001),
	e*s001-i001, i001*(s001-e*s011),
	f*s011-j011, j011*(s011-f*s001),
	e*s010-i010, i010*(s010-e*s110),
	f*s110-j110, j110*(s110-f*s010),
	e*s010-i010, i010*(s010-e*s011),
	f*s011-j011, j011*(s011-f*s010),
	e*s011-i011, i011*(s011-e*s111),
	f*s111-j111, j111*(s111-f*s011),
	e*s100-i100, i100*(s100-e*s110),
	f*s110-j110, j110*(s110-f*s100),
	e*s100-i100, i100*(s100-e*s101),
	f*s101-j101, j101*(s101-f*s100),
	e*s101-i101, i101*(s101-e*s111),
	f*s111-j111, j111*(s111-f*s101),
	e*s110-i110, i110*(s110-e*s111),
	f*s111-j111, j111*(s111-f*s110));
-- Try to decompose! 
time bcd = BPD (reactionsIdeal + ideal(e)); 
use R;
time bcd2 = BPD (reactionsIdeal + ideal(s000)); 
use R;
time bcd3 = BPD (reactionsIdeal + ideal(s100)); 
