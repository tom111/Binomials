csect = l -> (
     n := 0;
     R := ring l#0;
     answer := ideal (1_R);
     while #l>0 do (
	  l1 = l#0;
	  l = drop(l,1);
	  n = n+1;
	  << n << "\n";
	  answer = intersect (answer,l1);
	  );
     return answer;
     )
	  