load "Binomials.m2";
-- Macaulay 2 Code for the Commuting Birth and Death Ideal:
-- m = 2 ,n = 3 
S = QQ[R00,U00,R01,D01,U01,R02,D02,U02,R03,D03,R10,L10,U10,R11,L11,D11,U11,R12,L12,D12,U12,R13,L13,D13,L20,U20,L21,D21,U21,L22,D22,U22,L23,D23];
I = ideal (U00*R01-R00*U10,R01*D11-D01*R00,D11*L10-L11*D01,L10*U00-U10*L11,U01*R02-R01*U11,R02*D12-D02*R01,D12*L11-L12*D02,L11*U01-U11*L12,U02*R03-R02*U12,R03*D13-D03*R02,D13*L12-L13*D03,L12*U02-U12*L13,U10*R11-R10*U20,R11*D21-D11*R10,D21*L20-L21*D11,L20*U10-U20*L21,U11*R12-R11*U21,R12*D22-D12*R11,D22*L21-L22*D12,L21*U11-U21*L22,U12*R13-R12*U22,R13*D23-D13*R12,D23*L22-L23*D13,L22*U12-U22*L23);

-- The following ideal is the intersection of the radicals of 
-- the cellular components. 

I23cellRad = ideal (D13*L23-L22*D23,U12*L22-U22*L23,D12*L22-L21*D22,U11*L21-U21*L22,D11*L21-L20*D21,U10*L20-U20*L21,R12*D13-R13*D23,D03*L13-L12*D13,U12*R13-R12*U22,R11*D12-R12*D22,U02*L12-U12*L13,D02*L12-L11*D12,U11*R12-R11*U21,R10*D11-R11*D21,U01*L11-U11*L12,D01*L11-L10*D11,U10*R11-R10*U20,U00*L10-U10*L11,R02*D03-R03*D13,U02*R03-R02*U12,R01*D02-R02*D12,U01*R02-R01*U11,R00*D01-R01*D11,U00*R01-R00*U10,D01*R03*R10*L12*U21*L22*D23-U01*R03*L10*R13*D21*L23*D23,U00*R02*R12*L13*L20*D22*U22-R00*D02*R13*L13*U20*U22*L23,R00*U01*R03*L10*R13*U20*L23*D23-U01*R03^2*R13*L13*U20*L23*D23,U00*R02*R03*R12*L13*L20*D22*D23-R00*D02*R03*R13*L13*U20*L23*D23,U00*R03*R10*L12*L20*U21*L22*D23-U00*R03*L12*R13*U21*L22*L23*D23,R00*D02*L10*R13*L13*D21*U22*L23-D02*R03*R13*L13^2*D21*U22*L23,R00*D03*L11*R13*U20*L21*D22*L23-U00*R03*L12*R13*L20*L22*D22*D23,R01*U02*L10*R11*R13*D21*U21*L23-D01*R02*R10*R12*L13*U21*U22*L23,D01*R02*R10*R12*L13*L20*D22*U22-D01*R02*R12*R13*L13*D22*U22*L23,D01*R03*R10*L12*L13*U21*L22*U22-U01*R03*L10*R13*L13*D21*U22*L23);

