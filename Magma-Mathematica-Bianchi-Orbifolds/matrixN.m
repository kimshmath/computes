ListN:=function(d,N);
r:=[];
for i in [-N..N] do
	for j in [-N..N] do
		if i^2+d*j^2 le N^2 then
			Append(~r,i+j*Sqrt(-d));
		end if;
	end for;
end for;
return r;
end function;


MatrixN:=function(d,N);
_<x> := PolynomialRing(Rationals());
F<t> := NumberField(x^2+d);
ZF := Integers(F);
r:=[];
for a in ListN(d,N) do
	for b in ListN(d,N) do
		for c in ListN(d,N) do
			if (b*c+1)/a in ZF then 
				Append(~r,Matrix(ComplexField(), 2, 2, [a,b, c,(b*c+1)/a]));
			end if;
		end for;
	end for;
end for;
return r;
end function;

MatrixN(1,1);

