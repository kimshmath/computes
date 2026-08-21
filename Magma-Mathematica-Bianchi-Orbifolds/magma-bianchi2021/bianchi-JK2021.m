/*

bianchi.m
functions for handling Bianchi groups

bianchi.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

intrinsic BianchiOrder(d :: RngIntElt) -> AlgAssVOrd
{
    An order O in a quaternion algebra such that the norm one group is the Bianchi group of Q(sqrt(-|d|)).
}

	R<x> := PolynomialRing(Rationals());
    d := Abs(d);
	K<alpha> := NumberField(x^2+d);
	ZK := MaximalOrder(K);
	
	B := QuaternionAlgebra<K|1,1>;
	O := Order([One(B),(One(B)+B.1)/2,(B.2+B.3)/2,(B.2-B.3)/2]);
	
	return O;
end intrinsic;

function QuatToMatrix(g)
	K := BaseField(Parent(g));
	return MatrixRing(K,2) ! [g[1]+g[2],g[3]+g[4],g[3]-g[4],g[1]-g[2]];
end function;

function MatrixToQuat(m,O)
	B<i,j,k> := Algebra(O);
	return (m[1,1]*(1+i)+m[2,2]*(1-i)+m[1,2]*(j+k)+m[2,1]*(j-k))/2;
end function;


/*

aux.m
Auxiliary and printing functions

aux.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

function epsilon(r,Precision)
	R := RealField(Precision);
	return 10^(-R!(r*Precision));
end function;

procedure PrintCircle(C,pr)
	R := RealField(pr);
	print "center", R!(C`Center)[1], R!(C`Center)[2],R!(C`Center)[3], " - radius", R!(C`Radius), " - ortho", R!(C`e3)[1], R!(C`e3)[2],R!(C`e3)[3];
end procedure;

procedure PrintSphere(S,pr)
	R := RealField(pr);
	print "center", R!(S`Center)[1], R!(S`Center)[2],R!(S`Center)[3], " - radius", R!(S`Radius);
end procedure;

procedure PrintInterv(I,pr)
	R := RealField(pr);
	print [R!I[i] : i in [1..#I]];
end procedure;

procedure PrintSizeExtDom(F,FE,IE)
	vprint Kleinian, 2: "#F",#F,"#FE",#FE,"#IE",#IE;
end procedure;

/*

kleinian.m
Generic functions for handling arithmetic Kleinian groups

kleinian.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "geometry/basics.m" : JtoP, ZerotoP;

DefaultPrecision := 100;
Rdef := RealField(DefaultPrecision);
epsdef := 10^(-Rdef!DefaultPrecision/2);
Hdef<Idef,Jdef,Kdef> := QuaternionAlgebra<Rdef | -1,-1>;

declare attributes AlgQuat : KlnI, KlnH, KlnV;

declare verbose Kleinian, 3;

/*
    INPUT
    B : a quaternion algebra over a number field
    vC : a split infinite place of the base field of B
    M : the 2*2 matrix ring over C
    MH : the 2*2 matrix ring over the ring of Hamiltonians
    center : the center of the conjugation
    pr : the precision

    OUTPUT
    a corresponding embedding of O into M into MH when normalise=false, and of O* / Z_F* into PSL_2(C) into MH* when normalize=true
*/
function ioo(B,vC,M,MH,center,pr)
	H := BaseRing(MH);
	aa := Evaluate(-Norm(B.1), vC : Precision := pr);
	sa := Sqrt(aa);
	bb := Evaluate(-Norm(B.2), vC : Precision := pr);
	bsa := bb*sa;
	P,Pinv := JtoP(center, M);
	return function(x,normalize) 
		m := Pinv*(M!
			[x1   + x2*sa,	x3 + x4*sa,
			x3*bb - x4*bsa,	x1 - x2*sa]
			)*P
		where x1 := Evaluate(x[1], vC : Precision := pr)
		where x2 := Evaluate(x[2], vC : Precision := pr)
		where x3 := Evaluate(x[3], vC : Precision := pr)
		where x4 := Evaluate(x[4], vC : Precision := pr);
        if normalize and Norm(x) ne 1 then
            scal := 1/Sqrt(Determinant(m));
            m *:= scal;
        end if;
        mat := MH![A,B,C,D] 
		where A := ( (a+Conjugate(d)+(b-Conjugate(c))*H.2) )/2
		where B := ( (b+Conjugate(c)+(a-Conjugate(d))*H.2) )/2
		where C := ( (c+Conjugate(b)+(d-Conjugate(a))*H.2) )/2
		where D := ( (d+Conjugate(a)+(c-Conjugate(b))*H.2) )/2
		where a := H!Re(m[1,1]) + H.1*Im(m[1,1])
		where b := H!Re(m[1,2]) + H.1*Im(m[1,2])
		where c := H!Re(m[2,1]) + H.1*Im(m[2,1])
		where d := H!Re(m[2,2]) + H.1*Im(m[2,2]);
        return mat;
        end function;
		/*
		Pinv*
		[x[1]+x[2]*Sqrt(a), x[3]+x[4]*Sqrt(a),
		x[3]*b-x[4]*b*Sqrt(a), x[1]-x[2]*Sqrt(a)]
		*P
		*/
end function;

//In the Fuchsian case, it is necessary that a is positive at some real place.
intrinsic KleinianInjection(B :: AlgQuat : Center := 0, H := Hdef, Redefine := false) -> Map,AlgQuat,BoolElt
{
    Initializes and returns an embedding of B into M_2(C) into M_2(H), conjugated according to Center.
    Also returns H and a boolean indicating whether B is Fuchsian or not.
}
if not assigned B`KlnI or Redefine then
	pr := Precision(BaseField(H));
	if Center eq 0 then
		Center := H.2;
	end if;
	F := BaseField(B);
	oo := SequenceToSet(InfinitePlaces(F));
	ooR := SequenceToSet(RealPlaces(F));
	ooC := oo diff ooR;
	_,ooRam := RamifiedPlaces(B);
	require #ooC le 1 : "The base field must have at most one complex place.";
	if #ooC eq 1 then
		require #ooR eq #ooRam : "The quaternion algebra must be ramified at all real places.";
		vC := Rep(ooC);
		fuchsian := false;
	else
		require #ooR eq #ooRam+1 : "The quaternion algebra must be ramified at all real places but one.";
		vC := Rep(ooR diff SequenceToSet(ooRam));
		fuchsian := true;
	end if;

	M := MatrixRing(ComplexField(pr),2);
	MH := MatrixRing(H,2);
	B`KlnI := ioo(B,vC,M,MH,Center,pr);
	B`KlnH := H;
    B`KlnV := vC;
end if;
return B`KlnI,B`KlnH, fuchsian;
end intrinsic;

function kleinianmatrix(x : Normalize := true) 
	B := Parent(x);
	if not assigned B`KlnI then
        error "No Kleinian group defined for x.";
    end if;
	return (B`KlnI)(x,Normalize);
end function;

intrinsic KleinianMatrix(x::AlgQuatElt : Normalize := true) -> AlgMatElt
{
    Returns the matrix of the quaternion x acting on the unit ball model of the hyperbolic 3-space.
}
    return kleinianmatrix(x : Normalize := Normalize);
end intrinsic;

function isscalar(x)
    return x eq Conjugate(x);
end function;

function DefiniteNorm(x : Facteur := 1, Center1 := 0, Center2 := 0, m := kleinianmatrix(x : Normalize := false), mready := false, Balance := 1) //represents d(g*Center1, Center2)
    if not mready then
        MR := Parent(m);
        h1 := ZerotoP(Center1, MR);
        _,h2i := ZerotoP(Center2, MR);
        m := h2i*m*h1;
    end if;
    B := Parent(x);
    pr := Precision(BaseField(B`KlnH));
    _,ramplaces := RamifiedPlaces(B);
    if ramplaces cmpeq [] or Balance eq 0 then
        term := 0;
    else
        nx := Norm(x);
        term := &+[Evaluate(nx, v : Precision := pr) : v in ramplaces];
    end if;
	return Facteur*(Norm(m[1,1])+Norm(m[1,2]) + Balance*term);
end function;

function DefiniteBilinearForm(x1, x2 : Facteur := 1, Center1 := 0, Center2 := 0, Balance := 1) //represents d(g*Center1, Center2)
	return Facteur*(DefiniteNorm(x1+x2 : Center1 := Center1, Center2 := Center2, Balance := Balance) - DefiniteNorm(x1: Center1 := Center1, Center2 := Center2, Balance := Balance) - DefiniteNorm(x2: Center1 := Center1, Center2 := Center2, Balance := Balance));
end function;

function dgm(O : Precision := DefaultPrecision, Center1 := 0, Center2 := 0, Facteur := 1, Balance := 1, ComputeHGM := false, HGM := 0, Matrices := [])
	R := RealField(Precision);
	B := Algebra(O);
	gens := ZBasis(O);
	n := #gens;
    if Matrices cmpeq [] then
        Matrices := [kleinianmatrix(gens[i] : Normalize := false) : i in [1..n]];
    end if;
    MR := Parent(Matrices[1]);
    if not ComputeHGM then
        h1 := ZerotoP(Center1, MR);
        _,h2i := ZerotoP(Center2, MR);
        rMatrices := [h2i*Matrices[i]*h1 : i in [1..n]];
    else
        rMatrices := [MR!0 : i in [1..n]];
    end if;
	DGM := MatrixRing(R,n) ! 0;
    for i := 1 to n do
        DGM[i,i] := 2*DefiniteNorm(gens[i] : Facteur := Facteur, Center1 := Center1, Center2 := Center2, m := rMatrices[i], mready := true, Balance := Balance);
    end for;
    for i := 1 to n do
        for j := i+1 to n do
            DGM[i,j] := DefiniteNorm(gens[i]+gens[j] : Facteur := Facteur, Center1 := Center1, Center2 := Center2, m := rMatrices[i]+rMatrices[j], mready := true, Balance := Balance) - (DGM[i,i] + DGM[j,j])/2; 
            DGM[j,i] := DGM[i,j];
        end for;
    end for;

	return DGM+HGM,gens,Matrices;
end function;

intrinsic DefiniteGramMatrix(O :: AlgAssVOrd : Precision := DefaultPrecision, Center1 := 0, Center2 := 0, Facteur := 1, Balance := 1, ComputeHGM := false, HGM := 0, Matrices := []) -> AlgMatElt,SeqEnum,SeqEnum
{
    Returns the Gram matrix of Q and the Z-basis of O with respect to which it was computed. Q is a positive definite quadratic form on O detecting elements sending Center1 close to Center2, scaled by Facteur.
} //represents d(g*Center1, Center2)
    return dgm(O : Precision := Precision, Center1 := Center1, Center2 := Center2, Facteur := Facteur, Balance := Balance, ComputeHGM := ComputeHGM, HGM := HGM, Matrices := Matrices);
end intrinsic;

intrinsic Covolume(B :: AlgQuat : Precision := DefaultPrecision div 10, zK2 := 0) -> FldReElt
{
    The covolume of the Kleinian group attached to a maximal order in B. The optional argument zK2 is the value at 2 of the Dedekind zeta function of the base field.
}
	R := RealField(Precision);
	pi := Pi(R);
	K := BaseField(B);
	ZK := MaximalOrder(K);
	DK := Discriminant(ZK);
    if zK2 eq 0 then
    	zK := LSeries(K : Precision := Precision);
	    zK2 := Evaluate(zK,2);
    end if;
	DB := RamifiedPlaces(B);
	if #DB ne 0 then
		phi := &*[Norm(p)-1 : p in DB];
	else
		phi := 1;
	end if;
	n := Degree(K);
	
	return Abs(R!DK)^(3/2) * zK2 * phi / (4*pi^2)^(n-1);
end intrinsic;

intrinsic Coarea(B :: AlgQuat : Precision := DefaultPrecision, zK2 := 0) -> FldReElt
{
    The coarea of the Fuchsian group attached to a maximal order in B. The optional argument zK2 is the value at 2 of the Dedekind zeta function of the base field.
}
	R := RealField(Precision);
	pi := Pi(R);
	K := BaseField(B);
	ZK := MaximalOrder(K);
	DK := Discriminant(ZK);
    if zK2 eq 0 then
    	zK := LSeries(K : Precision := Precision);
	    zK2 := Evaluate(zK,2);
    end if;
	DB := RamifiedPlaces(B);
	if #DB ne 0 then
		phi := &*[Norm(p)-1 : p in DB];
	else
		phi := 1;
	end if;
	n := Degree(K);
	
	return Abs(R!DK)^(3/2) * zK2 * phi / (2^(2*n-3)*pi^(2*n-1));
end intrinsic;

intrinsic Psi(N :: RngOrdIdl) -> RngIntElt
{
    The multiplicative Psi function such that Psi(p^n) = Norm(p)^(n-1)*(Norm(p)+1).
}
facto := Factorization(N);
psi := 1;
for f in facto do
	np := Norm(f[1]);
	psi *:= np^(f[2]-1)*(np+1);
end for;
return psi;
end intrinsic;

function displacement(g,pr)
    B := Parent(g);
    vC := B`KlnV;
    d := Evaluate(Norm(g), vC : Precision := pr);
    t := Evaluate(Trace(g), vC : Precision := pr)/Sqrt(d);
    delta := Sqrt(t^2-4);
    a := (t+delta)/2;
    b := (t-delta)/2;
    return 2*Log(Max(Abs(a), Abs(b)));
end function;

intrinsic Displacement(g : Precision := DefaultPrecision) -> FldReElt
{
    The displacement of g acting on the hyperbolic 3-space.
}
    return displacement(g,Precision);
end intrinsic;



/*

enumeration.m
procedures for enumerating elements of arithmetic Kleinian groups

enumeration.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../kleinian.m" : isscalar, dgm;

/*
    INPUT
    O : an order in a quaternion algebra
    Lat : a reference for storing the result lattice
    TZB : a reference for storing the Z-basis
    nzb : a reference for storing the cardinality of the basis
    pr : the precision
    factor : a scaling factor for the quadratic form

    OPTIONAL
    Center1, Center2 : the centers of the quadratic form

    Initializes the lattice obtained by O equipped with the positive definite quadratic form with centers Center1, Center2.
*/
procedure InitializeLattice(O, ~Lat, ~TZB, ~nzb, pr, factor, ~HGM, ~basismat : Center1 := 0, Center2 := 0, Balance := 1)
    if HGM eq 0 then
        HGM,ZB,basismat := dgm(O : Precision := pr, Facteur := 4*factor, Center1 := Center1, Center2 := Center2, Balance := Balance, ComputeHGM := true, Matrices := basismat);
    end if;
    DGM,ZB,basismat := dgm(O : Precision := pr, Facteur := 4*factor, Center1 := Center1, Center2 := Center2, Balance := 0, HGM := HGM, Matrices := basismat);
    ispd := IsPositiveDefinite(DGM);
    if not ispd then 
        print "\nTHE QUADRATIC FORM IS NOT POSITIVE DEFINITE !!!";
        TZB := [];
        return;
    end if;

    nzb := #ZB;
    Gram2,T := LLLGram(DGM : Fast := 1, Proof := false);
    TZB := [ &+[T[i,k]*ZB[k] : k in [1..nzb]] : i in [1..nzb]];

    Lat := LatticeWithGram(Gram2);
end procedure;

/*
    INPUT
    x : the element of order to be processed
    order : an order in a quaternion algebra
    ZK : the base ring of order
    Enum : a reference for storing the elements of the group
    partialgpelt : a reference to a counter
    grouptype : an integer specifying which group is considered : 1 = norm one, 2 = units, 3 = normalizer
    bp : a bound on the primes to be stored
    primes : a reference for storing the elements whose norm generates a prime ideal
    maxp : a reference to a counter
    allowsq : a boolean specifying whether units with square norm should be accepted
    fuchsian : a boolean specifying whether the group is a Fuchsian group

    Stores x (maybe scaled) in the relevant container
*/
procedure ProcessVector(x, order, ZK, ~Enum, ~partialgpelt, grouptype, bp, ~primes, ~maxp, allowsq, fuchsian)
    nx := Norm(x);
    if isscalar(x) or nx eq 0 then
        return;
    end if;
    if Abs(NormAbs(nx)) eq 1 then
        if (nx eq 1 or (IsSquare(nx) and allowsq)) then
            x := x/Sqrt(nx);
            if x in order and not x in Enum and (not fuchsian or IsTotallyPositive(nx)) then
                Include(~Enum, x);
                partialgpelt +:= 1;
            end if;
        elif allowsq and grouptype ge 2 /*Units or Maximal*/ and (not fuchsian or IsTotallyPositive(nx)) then
            Include(~Enum, x);
        end if;
    else
        if grouptype eq 3 and order^x eq order and (not fuchsian or IsTotallyPositive(nx)) then
            Include(~Enum, x);
        end if;
        if Abs(NormAbs(nx)) le bp and IsPrime(nx*ZK) and (not fuchsian or IsTotallyPositive(nx)) then
            inprimes := false;
            ip := 1;
            while not inprimes and ip le maxp do
                p := primes[ip];
                if Norm(p)*ZK eq nx*ZK then
                    inprimes := true;
                end if;
                ip := ip+1;
            end while;
            if not inprimes then
                Append(~primes,x);
                maxp := maxp+1;
            end if;
        end if;
    end if;
end procedure;

/*
    INPUT
    Enum : a reference for storing the enumerated group elements
    u : a reference for the bound on the quadratic form
    ZB : the Z-basis of order corresponding to the lattice Lat
    nzb : the cardinality of ZB
    Lat : a reference to the lattice in which the enumeration should be performed
    totalvect : a reference to a counter
    totalgpelt : a reference to a counter
    NbEnum : the desired number of group elements
    stepu : a reference to the increment on the bound on the quadratic form
    order : the order containing the relevant group
    factor : the scaling factor of the quadratic form
    primes : a reference for storing elements whose norm generates a prime ideal
    ZK : the base ring of order
    bp : a bound on the primes to be stored
    grouptype : an integer specifying which group is considered : 1 = norm one, 2 = units, 3 = normalizer
    allowsq : a boolean specifying whether units with square norm should be accepted
    divadapt : a reference to a counter to automatically adapt the value of stepu
    fuchsian : a boolean specifying whether the group is a Fuchsian group
    randomized : a boolean specifying whether the enumeration is randomized at finite places

    Enumerates elements of the group corresponding to small vectors in Lat
*/
procedure Enumerate(~Enum,~u,ZB,nzb,~Lat,~totalvect,~totalgpelt, NbEnum, ~stepu, order, factor, ~primes, ZK, bp, grouptype, allowsq, ~divadapt, fuchsian, randomized)
    maxp := #primes;
	partialvect := 0;
	partialgpelt := 0;
    if NbEnum eq 0 then
        maxvenum := 1000;
    else
        maxvenum := 10000;
    end if;
	t := Cputime();
	nbproc := 0;
    repeat
		if u eq 0 then
            P := ShortVectors(Lat,stepu : Prune := [Max(0.5,(nzb-i)/nzb*1.) : i in [1..nzb]], Max := maxvenum+2);
		else
			P := ShortVectorsProcess(Lat,u,u+stepu);
		end if;
		nbproc +:= 1;
		u +:= stepu;
        if nbproc gt 1 then vprintf Kleinian, 2: "*"; end if;
		nm := 0;
        j := 1;
		while (Type(P) ne SeqEnum or j le #P) and nm ne -1 and (NbEnum ne 0 or partialvect lt maxvenum) and (NbEnum ge 1 or partialgpelt lt 11) do
            if Type(P) eq SeqEnum then
			    v,nm := Explode(P[j]);
            else
                v,nm := NextVector(P);
            end if;
            j +:= 1;
			x := &+[Round(v[i])*ZB[i] : i in [1..nzb]];
			partialvect +:= 1;
            ProcessVector(x, order, ZK, ~Enum, ~partialgpelt, grouptype, bp, ~primes, ~maxp, allowsq, fuchsian);
            if partialvect mod 1000 eq 0 then vprintf Kleinian, 2: "."; end if;
            if partialvect mod 10000 eq 0 then vprintf Kleinian, 3: "%o", partialgpelt; end if;
		end while;
    until partialgpelt ge NbEnum;

if NbEnum le 1 and not randomized then
    if partialvect ge 900 then
        stepu /:= (100+5/divadapt)/100;
    end if;
    if partialvect ge 200 then
        stepu /:= (100+2/divadapt)/100;
    end if;
    if partialvect ge 60 then
        stepu /:= (100+1/divadapt)/100;
    end if;
    if partialvect le 1 then
        stepu *:= (100+7/divadapt)/100;
    end if;
    if partialvect le 10 then
        stepu *:= (100+4/divadapt)/100;
    end if;
    if partialvect le 20 then
        stepu *:= (100+1/divadapt)/100;
    end if;
    divadapt +:= 1/9;
end if;

	totalvect +:= partialvect;
	totalgpelt +:= partialgpelt;
    vprintf Kleinian, 3: "(%o)", partialvect;
    if partialgpelt gt 0 then vprintf Kleinian, 2: "[+%o] ", partialgpelt; end if;
    vprintf Kleinian, 3: "stepu = %o\n", RealField(5)!stepu;
end procedure;



/*

normalisedbasis.m
functions implementing the Normalized Basis Algorithm for computing a Dirichlet domain for a Kleinian group

normalizedbasis.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../geometry/basics.m" : IsometricSphere, EndPoints, PointInCircle, sqrnorm, action, ZerotoP, Circle;
import "../geometry/exteriordomains.m" : UpdateExteriorDomain, IsInExteriorDomain, IntervalOfCircle;
import "../aux.m" : PrintSizeExtDom, epsilon;
import "../geometry/intervals.m" : PointInInterval, LengthInterval;
import "../geometry/volumes.m" : PolyhedronVolume, PolyhedronArea, ComputeZetas, VolumeDisc;
import "../geometry/random.m" : RadiusDisc, RadiusBall, RandomHyperbolicDisc, RandomHyperbolicBall, RandomInInterval, randprod;
import "enumeration.m" : InitializeLattice, Enumerate;
import "../kleinian.m" : kleinianmatrix, isscalar, Hdef, Rdef, DefaultPrecision;

/*
    Returns the normalized boundary of the exterior domain with faces F
*/
function NormalizedBoundary(F)
	return [f`g : f in F];
end function;

/*
    INPUT
    g : an element of the group
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Adds g to the normalized boundary of the exterior domain, for the routine KeepSameGroup
*/
procedure AddKSG(g, ~F, ~FE, ~IE, eps12, eps13, eps110)
    nbdel := 0;
    s := IsometricSphere(g,eps12);
    UpdateExteriorDomain(~F, ~FE, ~IE, s, 0, ~nbdel, eps12, eps13, eps110);
    
    s := IsometricSphere(g^(-1),eps12);
    UpdateExteriorDomain(~F, ~FE, ~IE, s, 0, ~nbdel, eps12, eps13, eps110);
end procedure;

/*
    INPUT
    G : a reference to the normalized boundary of the current exterior domain
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Runs the routine KeepSameGroup
*/
procedure KeepSameGroup(~G,~F,~FE,~IE,eps12, eps13, eps110)
vprint Kleinian: ">>>>>>>>>> KeepSameGroup";
S := SetToSequence(G);
repeat
    add := 0;
	for gamma in S do
		_,delta := Reduce(gamma, F : eps12 := eps12, Word := false);
		gammabar := delta*gamma;
		if not isscalar(gammabar) then
            add +:= 1;
            AddKSG(gammabar, ~F, ~FE, ~IE, eps12, eps13, eps110);
		end if;
	end for;
    vprint Kleinian, 2: "successful reductions :", add;
	PrintSizeExtDom(F,FE,IE);
    S := NormalizedBoundary(F);
until add eq 0;
G := SequenceToSet(S);
end procedure;

/*
    INPUT
    g : an element of the group
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    e : a reference to the index of an edge intersecting Int(g) (optional : 0=none, currently not used)
    G : a reference to the normalized boundary of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Adds g to the normalized boundary of the exterior domain, for the routine CheckPairing
*/
procedure AddP(g, ~F, ~FE, ~IE, ~e, ~G, eps12, eps13, eps110)
    nbdel := e;
    s := IsometricSphere(g,eps12);
	UpdateExteriorDomain(~F, ~FE, ~IE, s, /*e,*/0, ~nbdel, eps12, eps13, eps110);
    Include(~G,g);
    e -:= nbdel;

    nbdel := e;
    s := IsometricSphere(g^(-1), eps12);
	UpdateExteriorDomain(~F, ~FE, ~IE, s, 0, ~nbdel, eps12, eps13, eps110);
    Include(~G, g^(-1));
    e -:= nbdel;
end procedure;

/*
    INPUT
    G : a reference to the normalized boundary of the current exterior domain
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    allpaired : a reference for storing a boolean indicating whether the exterior domain has a face pairing
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    OPTIONAL
    Method : repairing method : Reduction | LengthThree

    Runs the routine CheckPairing
*/
procedure CheckPairing(~G,~F,~FE,~IE,~allpaired,eps12,eps13,eps110 : Method := "Reduction")
vprint Kleinian: ">>>>>>>>>> CheckPairing :", Method, "method";
allpaired := true;
repairing := 0;
ie := 1;
nfe := #FE;
while ie le nfe and ie le #FE do
    e := FE[ie];
	if Method eq "Reduction" then
		Sz1 := EndPoints(e);
		Sz := {z : z in Sz1 | sqrnorm(z) lt 1-eps110};
		if #Sz lt 2 then
			theta := PointInInterval(e[2]);
			z1 := PointInCircle(e[1], theta);
			Include(~Sz, z1);
		end if;
            if #Sz ne 0 and not IsInExteriorDomain(Rep(Sz),F,eps110) then
                error ">>>>>>>>>  INVALID EDGE !!!!!";
            end if;
		for z1 in Sz do
			for f in e[3] do
                if f le #F and ie gt 0 then
                    gamma := F[f]`g;
                    if not IsInExteriorDomain(action(F[f]`Matrix , z1), F, eps110) then
                        allpaired := false;
                        _, delta := Reduce(gamma, F : eps12 := eps12, z := z1, Word := false);
                            gamma := delta*gamma;
                    
                            if not isscalar(gamma) then
                                repairing +:= 1;
                                AddP(gamma, ~F, ~FE, ~IE, ~ie, ~G, eps12, eps13, eps110);
                            end if;
                    end if;
                end if;
			end for;
		end for;
	elif Method eq "LengthThree" then
		Faces := SetToSequence(e[3]);
		g1 := F[Faces[1]]`g;
		g2 := F[Faces[2]]`g;
		gamma := g1 * g2^(-1);
        found := false;
        for g in G do
            if isscalar(gamma*g^(-1)) then
                found := true;
                break;
            end if;
        end for;
		if not isscalar(gamma) and not found then
			if not isscalar(g1*g2) then
				allpaired := false;
                repairing +:= 1;
			end if;
            AddP(gamma, ~F, ~FE, ~IE, ~ie, ~G, eps12, eps13, eps110);
		end if;
	else
		error "Invalid Pairing Method";
	end if;
    ie +:= 1;
end while;
vprint Kleinian, 2: "allpaired", allpaired, "--- repairing :", repairing;
PrintSizeExtDom(F,FE,IE);
end procedure;

intrinsic myIndex(LG :: SeqEnum, InSubgroup :: UserProgram) -> RngIntElt, SeqEnum, SeqEnum
{
    Returns the index, a set of left cosets and a set of generators, of the finite index subgroup G' in G, where G is generated by LG and InSubgroup tests whether an element is in G'.
}
  B := Parent(LG[1]);
  S1 := [One(B)];
  S1new := [One(B)];
  S2 := {B |};
    while not S1new cmpeq []  do

      S1next := [];

      for s in S1new do
        for g in LG do
          x := s*g;
          insg := false;

          for t in (S1 cat S1next) do
            if InSubgroup(x*t^(-1)) then
                insg := true;
			    Include(~S2,x*t^(-1));
            end if;
          end for;

          if not insg then
            Append(~S1next,x);
          end if; 

        end for; 
      end for; 

      S1 cat:= S1next;
      S1new := S1next;

    end while;
    S3 := SetToSequence(S2);
  return #S1, S1, S3; 
end intrinsic;

/*
    INPUT
    g : an element of the group
    F : a reference to the faces of the current exterior domain
    FE : a reference to the finite edges of the current exterior domain
    IE : a reference to the infinite edges of the current exterior domain
    G : a reference to the normalized boundary of the current exterior domain
    eps12 : a small value for controlling approximation, 10^(-pr/2)
    eps13 : a small value for controlling approximation, 10^(-pr/3)
    eps110 : a small value for controlling approximation, 10^(-pr/10)

    Adds g to the normalized boundary of the exterior domain, for the main procedure
*/
procedure AddNB(g, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110)
    nbdel := 0;
    Include(~G, g);
    s := IsometricSphere(g,eps12);
    UpdateExteriorDomain(~F,~FE,~IE, s, 0, ~nbdel, eps12, eps13, eps110);

    Include(~G, g^(-1));
    s := IsometricSphere(g^(-1),eps12);
    UpdateExteriorDomain(~F,~FE,~IE, s, 0, ~nbdel, eps12, eps13, eps110);
end procedure;

intrinsic NormalizedBasis(O :: AlgAssVOrd : InitialG := [], NbEnum := 0, PeriodEnum := 100, Level := 1, BoundPrimes := -1, PairingMethod := "Reduction", GroupType := "NormOne", EnumMethod := "SmallBalls", Maple := false, zetas := [], zK2 := 0, Center := "Auto", index := 1, pr := DefaultPrecision) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum, FldReElt, SeqEnum, SeqEnum, FldReElt, FldReElt, FldReElt, RngIntElt, RngIntElt
{
    Computes a fundamental domain for the Kleinian group attached to the order O.

    Returns the normalized boundary of the domain, the faces, the finite edges, the infinite edges, the volume, elements with prime norm, the time spent enumerating, the time spent repairing, the time spent in KeepSameGroup, the number of enumerated vectors, the number of enumerated group elements.
}
nbit := 0;

if EnumMethod notin {"BigBall", "ManyBalls", "SmallBalls", "None"} then
    error "Invalid Enumeration Method.";
end if;

if GroupType eq "NormOne" then
    grouptype := 1;
elif GroupType eq "Units" then
    grouptype := 2;
elif GroupType eq "Maximal" then
    grouptype := 3;
    if not IsMaximal(O) then
        print "Warning : computing the normalizer of a non-maximal order, may have unexpected behaviour.";
    end if;
else
    error "Invalid Group Type";
end if;

if pr ne DefaultPrecision then
    R := RealField(pr);
    H := QuaternionAlgebra<R|-1,-1>;
else
    H := Hdef;
    R := Rdef;
end if;

if Center cmpeq "J" then
    Center := H!0;
elif Center cmpeq "Auto" then
    Center := 17/5*H.2 - 1/2*H.1 + 1/3*One(H);
end if;

B := Algebra(O);
K := BaseField(B);
ZK := MaximalOrder(K);
degK := Degree(K);

_,_,Fuchsian := KleinianInjection(B : Center := Center, H := Parent(Center), Redefine := true);

omega := K!ZK.2;

primes := [ B | ];

if Type(Level) eq RngIntElt then
	if not IsMaximal(O) then
		vprint Kleinian: ">>>>>>>>>> >>>>>>>>>> Computing for a maximal order first";
		OO := MaximalOrder(O);
		LG,_,_,_,_,primes := NormalizedBasis(OO : InitialG := InitialG, NbEnum := NbEnum, PeriodEnum := PeriodEnum, BoundPrimes := BoundPrimes, PairingMethod := PairingMethod, GroupType := GroupType, EnumMethod := EnumMethod, zetas := zetas, Maple := false, zK2 := zK2, Center := Center, pr := pr);
		index, Repres, Genes := myIndex(LG, func<x | x in O>);
		vprintf Kleinian, 2: ">>>>>>>>>> >>>>>>>>>> Subgroup has index %o in larger group, %o generators found\n", index, #Genes;
		vprint Kleinian: ">>>>>>>>>> >>>>>>>>>> Computing for the smaller order";
		InitialG := InitialG cat Genes;
		NbEnum := 1;
	end if;
end if;

vprint Kleinian: ">>>>>>>>>> NormalizedBasis";
H := B`KlnH;
MH := MatrixRing(H,2);
R := BaseField(H);
pr := Precision(R);
period := 1;

eps12 := epsilon(1/2,pr);
eps13 := epsilon(1/3,pr);
eps110 := epsilon(1/10,pr);

loo := R!7;

vprint Kleinian: ">>>>>>>>>> Initialization";

indexunits := 1;
randids := [];
if grouptype ge 2 then
   vprint Kleinian: "Computing the unit index";
   if grouptype eq 2 then
       U,f := UnitGroup(ZK); 
   else
       Ramf, Ramoo := Discriminant(B);
       U,f := SUnitGroup(Ramf);
   end if;
   ngu := Ngens(U);
   vprint Kleinian, 3 : "Unit group computed";
   pm := AbelianGroup([2]);
   Lhom := [hom<U -> pm | [pm!((1-Sign(Evaluate(K!f(U.i),v))) div 2) : i in [1..ngu]]> : v in RealPlaces(K)];
   Lker := [Kernel(hu) : hu in Lhom]; 
   if Lker eq [] then
       Utotpos := U;
   else
       Utotpos := &meet Lker;
   end if;
   U2 := sub<Utotpos | [Utotpos!(2*gene) : gene in Generators(U)]>;
   indexunits *:= Index(Utotpos, U2);
   vprint Kleinian, 2 : "index due to units :", Index(Utotpos, U2);
   if grouptype eq 3 then
       Cl, f := ClassGroup(K);
       if Ramoo cmpeq [] then
           Div := DivisorGroup(K)!0;
       else
           Div := &+[Divisor(v) : v in Ramoo];
       end if;
       Clplus, g := RayClassGroup(Div);
       M1 := sub<Clplus|[(g^(-1))(pp[1]) : pp in Factorization(Ramf)]>;
       J1, proj1 := quo<Clplus|M1>;
       mul2 := hom<J1 -> J1 | [x -> 2*x : x in Generators(J1)]>;
       J12 := Kernel(mul2);
       principality := hom<J12 -> Cl | [x -> (f^(-1))( g( (proj1^(-1))(J1!x) ) ) : x in Generators(J12)]>;
       M2 := Kernel(principality);
       ClB, proj2 := quo<J12 | M2>;
       indexunits *:= #ClB;
       vprint Kleinian, 2 : "index due to class group :", Index(J12, M2);

       ids := [g( (proj1^(-1))( J1 ! (proj2^(-1))(gen) ) ) : gen in Generators(ClB)];
       Append(~ids, Ramf);
       randids := SetToSequence({ idp[1] : idp in Factorization(lideal<O | Generators(idg)>), idg in ids });
       vprint Kleinian, 3 :  "Norms of randomising ideals :", [Norm(Norm(idp)) : idp in randids];
   end if;
   vprint Kleinian, 2: "total index :", indexunits;
end if;

if not Fuchsian then
	vprint Kleinian: "Computing the covolume";
	if Type(Level) ne RngIntElt then
		index *:= Psi(Level);
	end if;
	Covol := R!Covolume(B : zK2 := zK2)*index/indexunits;
	vprint Kleinian, 2: "covolume", RealField(10)!Covol;
else
	vprint Kleinian: "Computing the coarea";
	
	if Type(Level) ne RngIntElt then
		index *:= Psi(Level);
	end if;
	Covol := R!Coarea(B : zK2 := zK2)*index/indexunits;
	vprint Kleinian, 2: "coarea", RealField(10)!Covol, "rational", BestApproximation(Covol/Pi(RealField(50)), 1000);

    Coo := Circle(H!0,R!1,H.1);
end if;

DK := Discriminant(ZK);
DB := RamifiedPlaces(B);
if #DB ne 0 then
	db := &*[Norm(p) : p in DB];
else
	db := 1;
end if;
disc := Abs(R!(DK^4*db^2));
vprint Kleinian, 3: "disc", RealField(5)!disc;

if NbEnum eq 0 then
    NbEnum := Floor(0.3*Covol*Log(2+Covol))+1;//Floor(1.5*Covol)+1;
end if;
if degK eq 2 and db eq 1 then
    NbEnum *:= 2;
end if;
if EnumMethod eq "ManyBalls" then
    NbEnum div:= 4;
    NbEnum +:= 1;
end if;
vprint Kleinian, 3: "NbEnum = ", NbEnum;

if not Fuchsian and zetas eq [] then
    zetas := ComputeZetas(pr);
end if;

F := [];
FE := [];
IE := [];

Enum := {};

if Fuchsian then
	denomfactor := 1;
else
	denomfactor := 5000;
end if;

factor := R!(Max(Floor(disc*index/denomfactor),1/2)); //index should actually be the index of the orders here.
vprint Kleinian, 3: "factor :", factor;

propi := 6;
u := 0;
stepu := 4*factor;
if EnumMethod eq "SmallBalls" then
    magicmul := 18/10;
    stepu := 4*factor * (magicmul * (disc^(1/2))^(1/(2*degK)) + degK);
end if;
balance := stepu/(4*factor*degK);
vprint Kleinian, 3 : "balance", RealField(10)!balance;

HGM := 0;
basismat := [];
if EnumMethod eq "BigBall" then
    randomized := false;
    InitializeLattice(O, ~Lat, ~TZB, ~nzb, pr, factor, ~HGM, ~basismat : Balance := balance);
    if TZB eq [] then
        return [],[],[],[],0,[],[],0,0,0,0,0,0;
    end if;
end if;

if EnumMethod eq "ManyBalls" or EnumMethod eq "SmallBalls" then
    vprint Kleinian: "Computing radius for random centers";
    if Fuchsian then
        radenum := RadiusDisc(10*Max(Covol^(2+1/10),R!2));
    else
        radenum := RadiusBall(10*Max(Covol^(2+1/10),R!2), eps110);
    end if;
    vprint Kleinian, 3: "radenum", RealField(5)!radenum;
else
    radenum := R!0;
end if;

divadapt := 9/10;

totalvect := 0;
totalgpelt := 0;

allpaired := false;
Vol := 0;

G := {};

nochange := 0;

enumtime := Cputime();
enumtime *:= 0;
pairingtime := enumtime;
ksgtime := enumtime;

repeat
	nbit +:= 1;
	period -:= 1;
	if period le 0 then
        if EnumMethod ne "None" then
		t := Cputime();
        if EnumMethod eq "ManyBalls" then
            nbballs := NbEnum;
            localnbenum := 1;
            finboucle := func<b,nb | b gt nbballs>;
        elif EnumMethod eq "SmallBalls" then
            nbballs := 0;
            localnbenum := 0;
            finboucle := func<b,nb | nb ge NbEnum>;
            if Fuchsian then
                Ioo := IntervalOfCircle(Coo,F,false,{},eps12);
                loo := LengthInterval(Ioo);
            end if;
        elif EnumMethod eq "BigBall" then
            nbballs := 1;
            localnbenum := NbEnum;
            finboucle := func<b,nb | true>;
        end if;
        Enum := {};
        if EnumMethod eq "ManyBalls" or EnumMethod eq "SmallBalls" then
            vprint Kleinian, 3: "radenum", RealField(5)!radenum;
        end if;
        ball := 1;
        oldtotalgpelt := totalgpelt;
        vprint Kleinian: ">>>>>>>>>> Enumerate";
        vprint Kleinian, 3: "stepu =", RealField(5)!stepu;
        repeat
            allowsq := true;
            if EnumMethod eq "ManyBalls" or EnumMethod eq "SmallBalls" then
                if ball mod 10 lt propi and #IE ne 0 and (not Fuchsian or loo gt eps13) then
                    allowsq := false;
                    if Fuchsian then
                        enumcenter := RandomHyperbolicDisc(H,radenum/2);
                        theta := Random(Ioo);
                        x := PointInCircle(Coo, theta);
                    else
                        enumcenter := RandomHyperbolicBall(H,radenum/4,eps110);
                        ed := Random(1,#IE);
       	                theta := PointInInterval(IE[ed][2]);
                     	x := PointInCircle(IE[ed][1], theta);
                    end if;
                    x := (1-Exp(-radenum))*x;
                    hx := ZerotoP(x,MH);
                    enumcenter := action(hx, enumcenter);
                    vprintf Kleinian, 2: "i";
                else
                    vprintf Kleinian, 2: "r";
                    if Fuchsian then
                        enumcenter := RandomHyperbolicDisc(H,radenum);
                    else
                        enumcenter := RandomHyperbolicBall(H,radenum,eps110);
                    end if;
                end if;
                if (#IE eq 0 or (Fuchsian and loo ge eps13)) and #F ne 0 then
                    rbound := 2;
                else
                    rbound := 6;
                end if;
                if grouptype eq 3 and #randids ne 0 and Random(rbound) eq 0 then
                    randid := randprod(randids);
                    savHGM := HGM;
                    HGM := 0;
                    savbasismat := basismat;
                    basismat := [];
                    nab := (R!Norm(Norm(randid)))^(1/degK);
                    vprintf Kleinian, 3 : "{%o}", Norm(Norm(randid));
                    randomized := true;
                    stepu *:= nab;
                else
                    randid := O;
                    randomized := false;
                end if;
                InitializeLattice(randid, ~Lat, ~TZB, ~nzb, pr, factor, ~HGM, ~basismat : Center1 := enumcenter, Balance := balance);
                if TZB eq [] then
                    return [],[],[],[],0,[],[],0,0,0,0,0,0;
                end if;
                u := 0;
            end if;
            Enumerate(~Enum,~u,TZB,nzb,~Lat,~totalvect,~totalgpelt, localnbenum, ~stepu, O, factor, ~primes, ZK, BoundPrimes, grouptype, allowsq,~divadapt,Fuchsian,randomized);
            if randomized then
                HGM := savHGM;
                basismat := savbasismat;
                stepu /:= nab;
            end if;
            ball +:= 1;
        until finboucle(ball, totalgpelt-oldtotalgpelt);
	    vprintf Kleinian, 2: "\nTOTAL : %o enumerated vectors --- ", totalvect;
    	vprintf Kleinian, 2: "%o group elements (%o %%)\n", totalgpelt, RealField(5)!(100*totalgpelt/Max(totalvect,1));
	    vprint Kleinian, 3: "CPU time for enumeration: ", Cputime(t), " --- stepu =", RealField(5)!stepu;
		enumtime +:= Cputime(t);
        end if;
		
        for g in InitialG do
            if not isscalar(g) then
                Include(~Enum, g);
            end if;
        end for;

        for ied in IE do
            ieg := F[Rep(ied[3])]`g;
            if Trace(ieg)^2 eq 4*Norm(ieg) then
                vprint Kleinian, 3 : "Bianchi helper";
                x := ieg[1];
                y := ieg[3]-ieg[4];
                gamma := B![1,x*y,(y^2-x^2)/2,(x^2+y^2)/2];
                Include(~Enum, gamma);
                AddNB(gamma, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110);
                gamma := B![1,x*y*omega,(y^2-x^2)*omega/2,(x^2+y^2)*omega/2];
                Include(~Enum, gamma);
                AddNB(gamma, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110);
            end if;
        end for;
		
        vprint Kleinian: "Reduction of the new elements";
		for gamma in Enum do
			if #F ne 0  and PairingMethod ne "None" then
				_, delta := Reduce(gamma, F : eps12 := eps12, Word := false);
				gammabar := delta*gamma;
			else
				gammabar := gamma;
			end if;
			if not isscalar(gammabar) and not (gammabar in G) then
                AddNB(gammabar, ~F, ~FE, ~IE, ~G, eps12, eps13, eps110);
			end if;
		end for;
		PrintSizeExtDom(F,FE,IE);
		period := PeriodEnum;

    	t := Cputime();
	    KeepSameGroup(~G,~F,~FE,~IE,eps12, eps13, eps110);
    	ksgtime +:= Cputime()-t;
	end if;
	
	anf := #F;
	anfe := #FE;
	anie := #IE;

	t := Cputime();
	if PairingMethod eq "None" then
		allpaired := true;
	else
		CheckPairing(~G,~F,~FE,~IE,~allpaired,eps12,eps13,eps110 : Method := PairingMethod);
	end if;
	pairingtime +:= Cputime()-t;

    if not allpaired and #IE eq 0 and nochange le 1 then
        period +:= 1;
    end if;
	
	if #F eq anf and #FE eq anfe and #IE eq anie then
		period := 1;
		nochange +:= 1;
        propi := Min(propi+1,7);
	else
		nochange := 0;
        propi := Max(propi-1,3);
	end if;
	
    radenum +:= R!1/6;
    if #FE ne 0 then
        radenum +:= 1/5;
    end if;
	if nochange mod /*6 eq 4*/10 eq 9 then
		NbEnum *:= 2;
        //radenum +:= 1/8;
		vprint Kleinian, 3: "NbEnum :", NbEnum;
	end if;
	if nochange mod /*3 eq 2*/5 eq 4 then
		NbEnum *:= 2;
        //radenum +:= 1/8;
		vprint Kleinian, 3: "NbEnum :", NbEnum;
	end if;
	
	vprint Kleinian: ">>>>>>>>>> IsSubgroup";
	if not Fuchsian then
		if #F ne 0 and #IE /*eq 0*/ le 1 then
			if allpaired then
				Vol := PolyhedronVolume(F,FE, zetas);
				vprintf Kleinian: "subgroup of index %o (%o)\n", Round(Vol/Covol), RealField(6)!(Vol/Covol);
                vprint Kleinian, 3 : "Vol", Vol, "\nCov", Covol;
		else
				vprint Kleinian: "polyhedron is not a fundamental domain";
			end if;
		else
			vprint Kleinian: "polyhedron with infinite volume";
		end if;
        vprint Kleinian: "estimated progress:", RealField(5)!(50*Min(#F,3*Covol)/(3*Covol) + 50 - 50*Min(#IE,1+#F)/(1+#F)), "%";
	else //fuchsian
        Ioo := IntervalOfCircle(Coo,F,false,{},eps12);
        loo := LengthInterval(Ioo);
        vprint Kleinian, 2: "length at infinity =", 50*loo/Pi(RealField(5)), "%";
		if #F ne 0 and loo le eps13 then
			if allpaired or nochange ge 5 then
				Vol := PolyhedronArea(F,FE);
				vprintf Kleinian: "subgroup of index %o (%o)\n", Round(Vol/Covol), RealField(6)!(Vol/Covol);
			else
				vprint Kleinian: "polyhedron is not a fundamental domain";
			end if;
		else
			vprint Kleinian: "polygon with infinite area";
		end if;
        vprint Kleinian: "estimated progress:", RealField(5)!(100*(1-loo/(2*Pi(RealField(5))))^2*Min(#F,Covol)/Covol), "%";
	end if;

    if (Vol gt 0 and Vol lt Covol*9999/10000) then
        vprint Kleinian, 1 : "Error in the computation, rebuilding the exterior domain.";
        F,FE,IE := ExteriorDomain(F);
        allpaired := false;
    end if;
    if Fuchsian then
        F,FE,IE := ExteriorDomain(F);
    end if;

until (allpaired and Abs(Vol/Covol-1) lt 1/1000) or Abs(Vol/Covol-1) lt 1/10000000000;

if Maple then
    MapleFile(MapleDraw(MapleExteriorDomain([],FE,IE) : view := 1.), "FinalFDom");
    MapleFile(MapleDraw(MapleExteriorDomain(F,FE,IE) : view := 1.), "FinalFDomS");
    MapleFile(MapleDraw(MapleExteriorDomain([],FE,IE : Caption := true) : view := 1.), "FinalFDomC");
end if;

return NormalizedBoundary(F),F,FE,IE,Vol,primes,enumtime,pairingtime,ksgtime,totalvect,totalgpelt,u/(8*factor);
end intrinsic;



/*

presentation.m
functions for computing a presentation of a Kleinian group from a fundamental domain

presentation.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : epsilon;
import "../kleinian.m" : kleinianmatrix, isscalar;
import "../geometry/basics.m" : IntersectionAngle, PointInCircle, sqrnorm, scalar, action;
import "../geometry/intervals.m" : PointInInterval;

/*
    INPUT
    a : lower bound of the interval
    b : upper bound of the interval
    f : convex function [a,b] -> R
    eps : maximum error
    k : number of subdivisions (k>2)

    OUTPUT
    c, f(c) = min_[a,b](f)
*/
function Minim(a,b,f,eps,k) //k ge 3
 if Abs(b-a) le eps then
  return (a+b)/2,f((a+b)/2);
 else
  step := (b-a)/k;
  mini := f(a);
  minic := a;
  c := a+step;
  while c le b do
   fc := f(c);
   if fc lt mini then
    minic := c;
    mini := fc;
   end if;
   c +:= step;
  end while;
  return Minim(Max(a,minic-step),Min(b,minic+step),f,eps,k);
 end if;
end function;

/*
    INPUT
    I : [a1,b1,a2,b2,...] describing a union of intervals [a1,b1] U [a2,b2] U ...
    f : a function I -> R, convex on each [ai,bi]
    eps : maximum error
    k : number of subdivisions (k>2)

    OUTPUT
    x, f(x) = min_I(f)
*/
function MinimInterv(I,f,eps,k)
 minix := I[1];
 minif := f(minix);
 n := #I;
 i := 1;
 while i+1 le n do
  x,fx := Minim(I[i],I[i+1],f,eps,k);
  if fx lt minif then
   minix := x;
   minif := fx;
  end if;
  i +:= 2;
 end while;
 return minix,minif;
end function;

/*
    e : edge of a polyhedron
    eps : maximum error
    k : number of subdivisions (k>2)

    OUTPUT
    |x|^2 = min_e |.|^2, x
*/
function MinimEdge(e,eps,k)
 theta,d := MinimInterv(e[2],func<theta|sqrnorm(PointInCircle(e[1],theta))>,eps,k);
 return d, PointInCircle(e[1],theta);
end function;

/*
    INPUT
    FE : finite edges of a polyhedron
    pr : precision
    
    OUTPUT
    partition of FE into potential cycles, according to their minimal distance to 0

    REMARK
    Currently not used (too slow)
*/
function PotentialCycles(FE,pr)
    vprint Kleinian, 2: "Computing potential cycles";
    t := Cputime();
    eps := epsilon(1/25, pr);
    epsbig := epsilon(1/28, pr);
    nfe := #FE;
    distances := [MinimEdge(e,eps,5) : e in FE];
    index := [1..nfe];
    ParallelSort(~distances,~index);

    potentialcycles := [];
    i := 1;
    while i le nfe do
        potcyc := {index[i]};
        while i+1 le nfe and Abs(distances[i]-distances[i+1]) le epsbig do
            i +:= 1;
            Include(~potcyc, index[i]);
        end while;
        Append(~potentialcycles, potcyc);
        i +:= 1;
    end while;

    vprint Kleinian, 3 : "time potential cycles :", Cputime(t);
    return potentialcycles;
end function;

/*
    INPUT
    F : faces of the exterior domain
    FE : finite edges of the exterior domain
    pairing : F[pairing[i]] is the face paired with F[i]
    cycles : reference for storing the cycles
    words : reference for storing the words
    pr : precision
    usedist : boolean indicating whether PotentialCycles should be used

    Computes the cycles of the exterior domain : the list of edges, the cycle transformation, the corresponding word.
*/
procedure ComputeCycles(F,FE,pairing,~cycles,~words,pr,usedist)
eps := epsilon(1/3,pr);
one := Parent(F[1]`g)!1;
pi := Pi(RealField(pr div 3));
visited := [0 : e in FE]; //index of the face whose pairing transfo is used to send the edge to the next one. 0 : not visited yet ; -1 : not paired.
cycles := [];
words := [];
nfe := #FE;

if usedist then
    potentialcycles := PotentialCycles(FE,pr);
else
    potentialcycles := [{1..nfe}];
end if;

for potcyc in potentialcycles do
    restecyc := potcyc;
    while not IsEmpty(restecyc) do
        e := Rep(restecyc);
        if visited[e] eq 0 then
            cycle := [];
            word := [];
            e1 := e;
            f := Rep(FE[e][3]);
            cycletransfo := one;
            
            repeat 
                Append(~cycle, e1);
                f1 := Rep(FE[e1][3]);
                f2 := Rep(FE[e1][3] diff {f1});
                if isscalar( (F[f]`g)*(F[f1]`g) ) then
                    f1 := f2;
                end if;
                f := f1;

                cycletransfo := F[f]`g * cycletransfo;
                Append(~word, f);
                vprint Kleinian, 3 : "word", #word;

                theta := PointInInterval(FE[e1][2]);
                z := PointInCircle(FE[e1][1], theta);
                z1 := action(F[f]`Matrix,z);

                candidates := SetToSequence(restecyc meet F[pairing[f]]`Edges);
                ncan := #candidates;
                can := 1;
                found := false;
                while can le ncan and not found do
                    cir := FE[candidates[can]][1];
                    if Abs(sqrnorm(z1-cir`Center) - (cir`Radius)^2) le eps and Abs(scalar(z1-cir`Center,cir`e3)) le eps then
                        found := true;
                    else
                        can +:= 1;
                    end if;
                end while;

                if not found then
                    print "candidates", ncan;
                    error "did not find an adequate edge !";
                end if;

                visited[e1] := f;
                e1 := candidates[can];
            until e1 eq e; 
            
            for e1 in cycle do
                Exclude(~restecyc, e1);
            end for;
            Append(~cycles, <cycle,cycletransfo>);
            Append(~words, word);
        else
            print "Should not happen, please report." ;
            Exclude(~restecyc, e);
        end if;
    end while;
end for;
vprint Kleinian, 3 : "cycles", cycles, "words", words;
end procedure;

function order(g)
	B := Parent(g);
	if isscalar(g) then
		return 1;
	elif Trace(g)^2-4*Norm(g) eq 0 then
		return 0;
	else
		o := 1;
		gg := g;
		while not isscalar(gg) do
			gg *:= g;
			o +:= 1;
		end while;
		return o;
	end if;
end function;

intrinsic Presentation(F :: SeqEnum, FE :: SeqEnum, O :: AlgAssVOrd : UseDist := false) -> GrpFP, SeqEnum
{
    Computes a finite presentation for the subgroup of B* / Z(B)* with fundamental domain having faces F and edges FE. Returns a finitely presented group G and a list of elements of B* corresponding to the generators of G.
}
    vprint Kleinian, 1 : "Computing the presentation.";
	B := Algebra(O);
	H := B`KlnH;
	pr := Precision(BaseField(H));
    eps := epsilon(1/2, pr);
    zero := H!0;
	cycles := [];
	words := [];
	nf := #F;
	Fr := FreeGroup(nf);
	rels := [];
    pairing := [1..nf];

    distances := [sqrnorm(f`Center) : f in F];
    index := [1..nf];
    ParallelSort(~distances, ~index);
    
    potentialinverses := [];
    i := 1;
    while i le nf do
        potinv := [index[i]];
        while i+1 le nf and Abs(distances[i]-distances[i+1]) le eps do
            i +:= 1;
            Append(~potinv, index[i]);
        end while;
        Append(~potentialinverses, potinv);
        i +:= 1;
    end while;

    for potinv in potentialinverses do
        npi := #potinv;
        for g1 := 1 to npi do
            for g2 := g1 to npi do
                ig1 := potinv[g1];
                ig2 := potinv[g2];
                if isscalar(F[ig1]`g*F[ig2]`g) then
                    Append(~rels, Fr.ig1*Fr.ig2);
                    pairing[ig1] := ig2;
                    pairing[ig2] := ig1;
                end if;
            end for;
        end for;
    end for;

	ComputeCycles(F,FE,pairing,~cycles,~words,pr,UseDist);

	nword := #words;
	for iw := 1 to nword do
		w := words[iw];
		transfo := cycles[iw][2];
		rel := Fr!1;
		lw := #w;
		for i := 1 to lw do
			rel := Fr.w[i] * rel;
		end for;
		ord := order(transfo);
		if ord ne 0 then
			Append(~rels, rel^ord);
		end if;
	end for;
	
	return quo<Fr | rels>, [F[i]`g : i in [1..nf]];
end intrinsic;

function EvaluateWord(w, Gens)
    g := Parent(Gens[1])!1;
    sw := Eltseq(w);
    for i := 1 to #sw do
        g := g*(Gens[Abs(sw[i])]^(Sign(sw[i])));
    end for;
    return g;
end function;

intrinsic LiftPresentation(Pres :: GrpFP, Gens :: SeqEnum, O :: AlgAssVOrd, normone :: BoolElt) -> GrpFP, SeqEnum
{
    Lifts a presentation of a finitely generated subgroup G of B* from a presentation Pres and generators Gens for G/Z(G). G is the norm one group (normone=true) or the unit group (normone=false) of the order O. Returns a finitely presented group G and a list of elements of B* corresponding to the generators of G.
}

    B := Algebra(O);
    K := BaseField(B);
    ZK := Integers(K);
    U,f := UnitGroup(ZK); 
    fi := f^(-1);
    if normone then
        G := sub<U | fi(K!-1)>;
    else
        G := U;
    end if;

    nf := #Gens;
    nu := #Generators(G);
    ng := nf+nu;
    Fr := FreeGroup(ng);
    rels := [(Fr.(nf+1))^Order(G.1)];

    for i := nf+1 to ng do
        for j := 1 to i-1 do
            Append(~rels, Fr![-i,-j,i,j]);
        end for;
    end for;

    for r in Relations(Pres) do
        srel := Eltseq(LHS(r));

        if normone then
            urel := EvaluateWord(LHS(r), Gens);
            if urel eq 1 then
                mul := One(Fr);
            else
                mul := Fr.(nf+1);
            end if;
            Append(~rels, Fr!srel * mul);
        else
            urel := fi(EvaluateWord(LHS(r),Gens));
            useq := Eltseq(urel);
            Append(~rels, Fr!srel * &*[(Fr.(nf+i))^(-useq[i]) : i in [1..nu]]);
        end if;
    end for;

    return quo<Fr | rels>, Gens cat [f(G.j) : j in [1..nu]];
end intrinsic;




/*

reduction.m
functions implementing reduction algorithms for exterior domains

reduction.m is part of KleinianGroups, version 0.1 of May 20, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../geometry/basics.m" : Delta, action, sqrnorm;
import "../aux.m" : epsilon;
import "../kleinian.m" : kleinianmatrix, epsdef;

intrinsic ReducePoint(z :: AlgQuatElt, Boundary :: SeqEnum : eps12 := epsdef, DontUse := {}, Word := true, Evaluate := true) -> AlgQuatElt,SeqEnum,AlgQuatElt, RngIntElt
{
    Computes a point in the exterior domain with faces Boundary that is equivalent to z. Returns the equivalent point, the element delta such that delta*z is reduced as a word and as a quaternion, and the length of the reduction.
}
	H := Parent(z);
	R := BaseField(H);
	
	Rpr := RealField(10);
	n := #Boundary;
	error if n eq 0, "Empty boundary";
	B := Parent(Boundary[1]`g);
	reduced := false;
	deltaword := [];
	lengthw := 0;
	delta := B!1;
	
	while not reduced do
	
		i0 := 0;
        d := R!1;
		for i := 1 to n do
			if not (Boundary[i]`g in DontUse) then
                d1 := sqrnorm(z - Boundary[i]`Center)/(Boundary[i]`Radius)^2;
				if d ge (1+eps12)*d1 then
					d := d1;
					i0 := i;
				end if;
			end if;
		end for;
		
		if i0 eq 0 then
			reduced := true;
		else
		    z := action(Boundary[i0]`Matrix,z);
			if Word then
				Append(~deltaword,i0);
			end if;
			if Evaluate then
				delta := (Boundary[i0]`g)*delta;
			end if;
			lengthw +:= 1;
            if not Word and Trace(Boundary[i0]`g)^2 eq 4*Norm(Boundary[i0]`g) then
                gg := Boundary[i0]`g;
                zz := z;
                help := -1;
                repeat
                    help +:= 1;
                    z := zz;
                    gg := gg^2;
                    zz := action(kleinianmatrix(gg),z);
                    delta := gg * delta;
                until Delta(z,H!0) le (1+eps12)*Delta(zz,H!0);
                delta := gg^(-1)*delta;
            end if;
		end if;
		
	end while;
	
	Reverse(~deltaword);
	return z,deltaword,delta,lengthw; //Red(z) = delta*z, deltaword evaluates to delta.
end intrinsic;

intrinsic Reduce(gamma :: AlgQuatElt, Boundary :: SeqEnum : eps12 := epsdef, z := (Parent(gamma)`KlnH)!0, DontUse := {}, Word := true, Evaluate := true) -> SeqEnum,AlgQuatElt,AlgQuatElt, RngIntElt //Red(gamma) = delta*gamma, deltaword evaluates to delta.
{
    Computes the reduction of gamma with respect to the exterior domain with faces Boundary. Returns the element delta such that delta*gamma*z is in the exterior domain as a word and as a quaternion, the reduced point, and the length of the reduction
}
	z,deltaword,delta,length := ReducePoint(action((kleinianmatrix(gamma)) , z), Boundary : eps12 := eps12, DontUse := DontUse, Word := Word, Evaluate := Evaluate);
	return deltaword,delta,z,length;
end intrinsic;

intrinsic Word(gamma :: AlgQuatElt, Boundary :: SeqEnum, G :: GrpFP) -> GrpFPElt
{
    Returns the element in the finitely presented group G corresponding to the quaternion gamma. 
}
    R := Parent(Boundary[1]`Radius);
    eps := epsilon(1/2,Precision(R));
    word := Reduce(gamma^(-1), Boundary : eps12 := eps, Evaluate := false);
    g := One(G);
    for i := 1 to #word do
        g := g*G.(word[i]);
    end for;
    return g;
end intrinsic;




/*

basics.m
Basic geometric functions

basics.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : epsilon;
import "../kleinian.m" : kleinianmatrix, isscalar;

function vecprod(x,y)
	H := Parent(x);
	return H![x[2]*y[3]-x[3]*y[2] , x[3]*y[1]-x[1]*y[3] , x[1]*y[2]-x[2]*y[1] , 0];
end function;

function colinear(x,y,eps12)
	return Abs(x[2]*y[3]-x[3]*y[2]) le eps12 and Abs(x[3]*y[1]-x[1]*y[3]) le eps12 and Abs(x[1]*y[2]-x[2]*y[1]) le eps12;
end function;

function m(x, y, z)
	return (x[2]*y[3]-x[3]*y[2])*z[1] + (x[3]*y[1]-x[1]*y[3])*z[2] + (x[1]*y[2]-x[2]*y[1])*z[3];
end function;

function scalar(x,y)
	return x[1]*y[1]+x[2]*y[2]+x[3]*y[3];
end function;

function sqrnorm(x)
	return x[1]^2+x[2]^2+x[3]^2+x[4]^2;
end function;

Sphr := recformat<Center : AlgQuatElt , Radius : FldReElt, g : AlgQuatElt, Matrix : AlgMatElt, Edges : SetEnum >;

function Sphere(center, radius)
	error if radius lt 0, "the radius must be positive."; 
	return rec<Sphr | Center := center, Radius := radius>;
end function;

function PlaneBasis(N)
	H<i,j,k> := Parent(N);
	e1 := i*N;
	e1[4] := 0;
	if e1 eq 0 then
		e1+:=H!1;
	else
		e1 := e1/Sqrt(sqrnorm(e1));
	end if;
	e2 := vecprod(N,e1);
	e2 := e2/Sqrt(sqrnorm(e2));
	return e1,e2;
end function;

Crcl := recformat<Center : AlgQuatElt , Radius : FldReElt , e1 : AlgQuatElt, e2 : AlgQuatElt, e3 : AlgQuatElt>;

function Circle(center, radius, orthogonal)
	error if radius lt 0, "the radius must be positive.";
	error if orthogonal eq 0, "the orhogonal vector must be nonzero.";
	e1,e2 := PlaneBasis(orthogonal);
	return rec<Crcl | Center := center , Radius := radius , e1 := e1, e2 := e2, e3 := orthogonal>;
end function;

function AngleInPlane(x, e1, e2)//e1,e2 orthonormal
	R := BaseField(Parent(x));
	C<I> := ComplexField(R);
	z := scalar(x,e1)+I*scalar(x,e2);
	error if z eq 0, "The angle is not defined when x is orthogonal to <e1,e2>.";
	theta := Arg(z);
	if theta lt 0 then theta := theta + 2*Pi(R); end if;
	return theta;
end function;

function PointInCircle(C, theta)
	return C`Center+C`Radius*(Cos(theta)*C`e1+Sin(theta)*C`e2);
end function;

function Delta(u,v)
	return sqrnorm(u-v)/((1-sqrnorm(u))*(1-sqrnorm(v)));
end function;

function Distance(u, v)
	return Argcosh(1+2*Delta(u,v));
end function;

function action(g, w)
	HH := Parent(w);
	pr := Precision(BaseField(HH));
	gw := (g[1,1]*w+g[1,2])/(g[2,1]*w+g[2,2]);
	gw[4] := 0;
	if sqrnorm(gw) ge 1 then
		gw := gw/Sqrt(sqrnorm(gw));
		gw *:= HH!(1 - epsilon(9/10,pr));
	end if;
	return gw;
end function;

intrinsic '*'(g::AlgMatElt, w::AlgQuatElt) -> AlgQuatElt
{
    Action of g on the point w in the unit ball model of the hyperbolic 3-space
}
    return action(g, w);
end intrinsic;

function MatrixIsometricSphere(m)
	error if sqrnorm(m[2,1]) le 0, "This element has no isometric sphere.", m, Norm(m[2,1]), sqrnorm(m[2,1]);
	center := -(1/m[2,1]) * m[2,2];
	center[4] := 0;
	
	return rec<Sphr | Center := center, Radius := 1/Sqrt(sqrnorm(m[2,1])), Matrix := m>;
end function;

function IsometricSphere(g, eps)
	S := MatrixIsometricSphere(kleinianmatrix(g));
	S`g := g;
	return S;
end function;

function ZerotoP(p, MR)
	H := BaseRing(MR);
    if p eq 0 then
        r2 := 1;
    else
        r2 := 1-sqrnorm(p);
    end if;
    if r2 le 0 then
        vprint Kleinian : "WARNING, correction of p";
        return ZerotoP((1-epsilon(9/10,pr))*p, MR) where pr := Precision(BaseField(H));
    end if;
	ri := 1/Sqrt(r2);
	return ri*(MR![1,-p,Conjugate(p),-1]), ri*(MR![-1,p,-Conjugate(p),1]);
end function;

function JtoP(p, MR)
	C<I>:= BaseRing(MR);
	a := p[1]+I*p[2];
	t := p[3];
	error if t le 0, "p is not an element of H3.";
	st := Sqrt(t);
	return MR![st,a/st,0,1/st], MR![1/st,-a/st,0,st];
end function;

function IsInterior(w, S, eps12)
	return sqrnorm(w-S`Center) le (S`Radius)^2*(1+eps12);
end function;

function IsExterior(w, S, eps12)
	return sqrnorm(w-S`Center) ge (S`Radius)^2*(1-eps12);
end function;

function IntersectionAngle(S1,S2)
	cosa := (sqrnorm(S1`Center-S2`Center)-((S1`Radius)^2+(S2`Radius)^2)) / (2*S1`Radius*S2`Radius);
	error if Abs(cosa) gt 1, "The spheres do not intersect.";
	return Arccos(cosa);
end function;

function SpheresIntersection(S1, S2, eps12)
	N := S2`Center - S1`Center;
	D := sqrnorm(N);
	if D le eps12 then
		return rec<Crcl | Radius := -1. >; //Radius = -1 : empty set.  Warning, incorrect result if spheres are the same.
	end if;
	
	M := (S2`Center + S1`Center)/2;
	R1 := S1`Radius;
	R2 := S2`Radius;
	Rsqr := ((R1+R2)^2-D)*(D-(R1-R2)^2)/(4*D);
	if Rsqr lt 0 or (Rsqr lt eps12 and Trace(S1`g)^2 eq 4 and Trace(S2`g)^2 eq 4 and isscalar(S1`g*S2`g/(S2`g*S1`g))) then
		return rec<Crcl | Radius := -1. >;
	else
		return Circle(M+(R1^2-R2^2)/(2*D)*N, Sqrt(Rsqr), N);
	end if;
end function;

function PlanesIntersection(X1, N1, X2, N2)
	Y := vecprod(N1,N2);
	Z := vecprod(Y,N2);
	a := m(Y,N2,N1);
	b := scalar(N1,X1-X2);
	error if a eq 0, "The planes are parallel.";
	return X2+b/a*Z,Y; //point, direction.
end function;

function PointsToSphere(x,y,z)
	H := Parent(x);
	a := (y-x)[1];
	b := (y-x)[2];
	c := (z-x)[1];
	d := (z-x)[2];
	alpha := (sqrnorm(y)-sqrnorm(x))/2;
	beta := (sqrnorm(z)-sqrnorm(x))/2;
	D := a*d-b*c;
	if D eq 0 then return Sphere(x,BaseField(H)!0); end if;
	t1 := (d*alpha - b*beta)/D;
	t2 := (a*beta - c*alpha)/D;
	Y := H!t1 + t2*H.1;
	return Sphere(Y, Sqrt(sqrnorm(Y-x)));
end function;

function EndPoints(e)
	Interv := e[2];
	return {PointInCircle(e[1],Interv[2]), PointInCircle(e[1],Interv[1+(2 mod #Interv)])};
end function;

function BtoH(j,w)
	return (1/(1+w*j)) * (w+j);
end function;

function PerturbatedBtoH(j,w)
	if w eq j then
		return Parent(j)!(1000000000/1174263548);
	else
		z := BtoH(j,w);
		return z/(1174263548/1000000000*z+1);
	end if;
end function;

function SameSphere(S1, S2, eps)
	b := sqrnorm(S1`Center-S2`Center) lt eps^2
		and Abs(S1`Radius-S2`Radius) lt eps;
	return b;
end function;

function SameCircle(C1, C2, eps)
	b := sqrnorm(C1`Center-C2`Center) lt eps^2
		and Abs(C1`Radius-C2`Radius) lt eps
		and sqrnorm(vecprod((C1`e3),(C2`e3)))*C1`Radius*C2`Radius lt sqrnorm(C1`e3)*sqrnorm(C2`e3)*eps^2;//affaiblir cette condition en enlevant les rayons ?
	return b;
end function;



/*

exteriordomains.m
procedures for computing the exterior domain of a finite subset of a Kleinian group

exteriordomains.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../kleinian.m" : DefaultPrecision;
import "basics.m" : IsExterior, SphereCircleIntersection, AngleInPlane, IsInterior, PointInCircle, Sphere, SpheresIntersection, SameCircle, SameSphere, sqrnorm, colinear, vecprod, scalar, m;
import "random.m" : RandomInCircle;
import "intervals.m" : PointInInterval, IntersectionCompacts, LengthInterval;
import "../aux.m" : epsilon;

function IsInExteriorDomain(w,L,eps)
	for s in L do
		//if not IsExterior(w,s,eps12) then : inline
        if sqrnorm(w-s`Center) lt (s`Radius)^2*(1-eps) then
			return false;
		end if;
	end for;
	return true;
end function;

/*
    INPUT
    C : a circle
    S : a sphere
    interior : a boolean
    eps12 : a small real for handling approximation, 10^(-pr/2)

    OUTPUT
    The union of intervals in [0,2*Pi] corresponding to the points of C that are in the interior/exterior of S, according to 'interior'.
*/
function CutInterval(C, S, interior, eps12)
    CCenter := C`Center;
    Ce1 := C`e1;
    Ce2 := C`e2;
    Ce3 := C`e3;
    SCenter := S`Center;
	R1 := S`Radius;
	R2 := C`Radius;
	H := Parent(Ce3);
	R := BaseField(H);
	pi2 := 2*Pi(R);
	
	if R2 ge eps12 then //Avant : eps(6/10)
        
   //function SphereCircleIntersection(S, C, eps12) : inline
	N := CCenter - SCenter;
	D := sqrnorm(N);
	
    if D ge (R1+R2)^2 then
        if interior then
            return [];
        else
            return [R!0,pi2];
        end if;
    else 
        //à remplacer par des epsilons ?
        if R2 eq 0 then
            if D eq R1^2 then
                Inter := [CCenter];
            else
                Inter := [];
            end if;
        else
            
            if D le eps12 then //Avant : eps(1/3)
                if Abs(R1-R2) le eps12 then
                    p0 := PointInCircle(C,0);
                    Inter := [p0,p0,p0];
                else
                    Inter := []; //Warning : incorrect if the circle is a geodesic on the sphere
                end if;
            else
                
                M := (CCenter + SCenter)/2;
                Cent := M+(R1^2-R2^2)/(2*D)*N;
                
                if not colinear(N,Ce3,eps12) then

                    //Pt,Y := PlanesIntersection(C`Center,C`e3,Cent,N);
                    //function PlanesIntersection(X1, N1, X2, N2) : inline
                    Y := vecprod(Ce3,N);
                    a := m(Y,N,Ce3);
                    Z := vecprod(Y,N);
                    b := scalar(Ce3,CCenter-Cent);
                    Pt := Cent+b/a*Z;
                    //end function;
                    
                    A := sqrnorm(Y);
                    B := scalar(Y,Pt-SCenter);
                    CC := sqrnorm(Pt-SCenter)-R1^2;
                    
                    Delta := B^2-4*A*CC;
                    if Delta lt 0 then
                        Inter := [];
                    elif Delta/A gt eps12*R2 then //Avant : eps(2/3)
                        SD := Sqrt(Delta);
                        Inter := [Pt+((-B+SD)/(2*A))*Y,Pt-((B+SD)/(2*A))*Y];
                    else //Delta eq 0
                        vprint Kleinian, 1: "Warning : unique intersection";
                        ptinter := Pt-B/(2*A)*Y;
                        Inter := [ptinter];
                    end if;
                
                else //plans paralleles
                    if Abs(R1^2-R2^2-D) le eps12 then
                        p0 := PointInCircle(C,0);
                        Inter := [p0,p0,p0];
                    else
                        Inter := []; //faux si le cercle est entièrement inclus dans la sphere.
                    end if;
                end if;
            end if;
        end if;
    end if;
        //end function;
        //end inline
        
		//Inter := SphereCircleIntersection(S, C, eps12);
		AnglesInter := [AngleInPlane(x-CCenter, Ce1, Ce2) : x in Inter];
	else
		AnglesInter := [];
	end if;
	
	n := #AnglesInter;
	if n gt 2 then
		return [R!0,pi2];
	elif n le 1 then //dépend si à l'intérieur ou à l'extérieur : tester un point du cercle.
        //ptci := RandomInCircle(C);
        ptci := CCenter + R2*(3/5*Ce1 + 4/5*Ce2);

		if interior then
			correctpt := IsInterior(ptci, S, eps12);
		else
			correctpt := IsExterior(ptci, S, eps12);
		end if;
		if correctpt then
			return [R!0, pi2];
		else
			return [];
		end if;
		
	else //n=2
	
        //sort AnglesInter
        a1 := AnglesInter[1];
        a2 := AnglesInter[2];
        if a1 ge a2 then
            AnglesInter[1] := a2;
            AnglesInter[2] := a1;
        end if;

		theta := PointInInterval(AnglesInter);
		if interior then
			correctpt := IsInterior(PointInCircle(C, theta), S, eps12);
		else
			correctpt := IsExterior(PointInCircle(C, theta), S, eps12);
		end if;
		if correctpt then
			return [AnglesInter[1], AnglesInter[2]];
		else
			return [R!0, AnglesInter[1], AnglesInter[2], pi2];
		end if;
	end if;
end function;

function InteriorInterval(C, S, eps12)
	return CutInterval(C, S, true, eps12);
end function;

function ExteriorInterval(C, S, eps12)
	return CutInterval(C, S, false, eps12);
end function;

/*
    INPUT
    C : a circle
    L : a sequence of spheres
    USPhere : a boolean
    SetL : a set of indices indicationg the spheres in L to be ignored
    eps12 : a small real for handling approximation, 10^(-pr/2)

    OUTPUT
    The union of intervals in [0,2*Pi] corresponding to the set of points that are in the exterior of the spheres in L, and if USphere is set to true, that are also in the interior of the unit sphere.
*/
function IntervalOfCircle(C, L, USphere, SetL, eps12)
	H := Parent(C`e3);
	R := BaseField(H);
	pi2 := 2*Pi(R);
	
	Linterv := [];
	
	//inside the unit sphere
	if USphere then
		UnitSphere := Sphere(H!0,R!1);
		//Interv := InteriorInterval(C, UnitSphere, eps12);
		Interv := CutInterval(C, UnitSphere, true, eps12);
		Append(~Linterv, Interv);
	end if;
	
	//outside the spheres
	n := #L;
	for s := 1 to n do
		if not (s in SetL) then
			//Interv := ExteriorInterval(C, L[s], eps12);
            Interv := CutInterval(C, L[s], false, eps12);
			Append(~Linterv, Interv);
            if s mod 20 eq 19 then
                LInterv := [IntersectionCompacts(Linterv,pi2)];
                if LInterv eq [[]] then
                    return [];
                end if;
            end if;
		end if;
	end for;
	
	Lfin := IntersectionCompacts(Linterv,pi2);
	return Lfin;
end function;

function PointNextToInfinity(S,z,eps)
	z1 := (1-eps)*z;
	z1 := S`Center + (z1-S`Center)*S`Radius/Sqrt(sqrnorm(z1-S`Center));
	return z1;
end function;

/*
    INPUT
    F : a reference to the set of faces of the polyhedron
    E : a reference to a set of edges of the poyhedron
    S : a sphere
    FP : a reference for storing the faces affected by the operation
    start : the index of an edge going to be affected (optional, 0=none, currently unused)
    nbdel : a reference for storing the number of deleted edges before 'start' (used only with 'start')
    eps12 : a small real for handling approximation, 10^(-pr/2)
    eps13 : a small real for handling approximation, 10^(-pr/3)

    Modifies the previously existing edges of the polyhedron, according to cutting it with the half-space exterior to the sphere S
*/
procedure EatEdges(~F, ~E, S, ~FP, start, ~nbdel, eps12, eps13)
	pi2 := 2*Pi(Parent(eps12));
	n := #E;
	ToRemove := [];
    dfs := start ne {};
    if dfs then
        tovisit := start;
        visited := {};
    end if;
    e := 0;
	while (dfs and not IsEmpty(tovisit)) or (not dfs and e lt n) do
        if dfs then
            ExtractRep(~tovisit, ~e);
            Include(~visited, e);
        else
            e +:= 1;
        end if;
		//Interv := ExteriorInterval(E[e][1],S, eps12);
		Interv := CutInterval(E[e][1],S,false,eps12);
        lg := LengthInterval(E[e][2]);
		E[e][2] := IntersectionCompacts([E[e][2],Interv],pi2);
        if LengthInterval(E[e][2]) lt lg then
            FP join:= E[e][3];
            if dfs then
                for f in E[e][3] do
                    tovisit join:= F[f]`Edges diff visited;
                end for;
            end if;
        end if;
		if LengthInterval(E[e][2]) le eps13 then
			Append(~ToRemove, e);
		end if;
	end while;
    if dfs then
        Sort(~ToRemove);
    end if;
	ntr := #ToRemove;
    limit := nbdel;
    nbdel := 0;
	for i := 1 to ntr do
		Remove(~E, ToRemove[i]-i+1); //shift because of previous suppressions.
        if ToRemove[i] le limit then
            nbdel +:= 1;
        end if;
	end for;
end procedure;

/*
    INPUT
    F : faces of the polyhedron
    S : a sphere
    FP : indices of relevant faces
    eps12 : a small real for handling approximation, 10^(-pr/2)

    OUTPUT
    The new finite edges and the new infinite edges created when cutting the polyhedron with S
*/
function NewEdges(F, S, FP, eps12, eps13)
	H := Parent(S`Center);
	R := BaseField(H);
	UnitSphere := Sphere(H!0,R!1);
	
	NFE := [];
	n := #F;
	for f in FP do
		C := SpheresIntersection(F[f],S,eps12);
		if C`Radius ge eps13 then //Avant : eps(1/3)
			Interv := IntervalOfCircle(C, F, true, {f}, eps12);
			if LengthInterval(Interv) ge eps13 then //Avant : eps(1/3)
				Append(~NFE, <C,Interv,{f,n+1}>);
			end if;
		end if;
	end for;
	
	C := SpheresIntersection(UnitSphere,S,eps12);
	if C`Radius ge eps13 then
		Interv := IntervalOfCircle(C, F, false, {}, eps12);
		if LengthInterval(Interv) ge eps13 then //Avant : eps(1/3)
			NIE := [<C,Interv,{n+1}>];
		else
			NIE := [];
		end if;
	else //should never happen
		NIE := [];
	end if;
	
	return NFE,NIE;
end function;

/*
    INPUT
    F : a reference to the faces of the polyhedron
    E : a reference to the edges of the polyhedron
    NE : the new egdes of the polyhedron
    nbF : the number of faces of the polyhedron
    eps12 : a small real for handling the approximation, 10^(-pr/2)
    eps110 : a small real for handling the approximation, 10^(-pr/10)

    Removes the redundancy in the edges of the polyhedron.
*/
procedure EliminateMultipleEdges(~F, ~E, NE, nbF, eps12, eps110)
	R := Parent(eps12);
	n := #E;
	nn := #NE;
	for nedge := 1 to nn do
		old := false;
		for edge := 1 to n do
			if SameCircle(NE[nedge][1],E[edge][1],eps12) then
				//que faire avec l'intervalle ? Prendre la réunion ? L'intersection ? Ne garder que le "vieux" (actuellement) ?
				E[edge][3] := E[edge][3] join NE[nedge][3];
				old := true;
				break;
			end if;
		end for;
		if not old then
			Append(~E, NE[nedge]);
		end if;
	end for;
	
	n := #E;
	for edge := 1 to n do
        nbFe := #E[edge][3];
		if nbFe gt nbF then
			candidates := [];
            candidatesL := [];
			theta := PointInInterval(E[edge][2]);
			x := PointInCircle(E[edge][1], theta);
			STest := Sphere(x,eps110);
			for f in E[edge][3] do
				CTest := SpheresIntersection(F[f],STest,eps12);
				IntervTest := IntervalOfCircle(CTest, F, true, {f}, eps12);
				LTest := LengthInterval(IntervTest);
                Append(~candidates, f);
                Append(~candidatesL, R!LTest);
			end for;
			//Sort(~candidates, func<x,y | y[2]-x[2]>); //decreasing order wrt the second variable.
			//E[edge][3] := {c[1] : c in candidates[1..nbF]}; 
            if nbF eq 1 then 
                _,imax := Max(candidatesL); 
                E[edge][3] := {candidates[imax]}; 
            else //nbF = 2 

                //max and second
                if candidatesL[1] gt candidatesL[2] then
                    imax1 := 1;
                    imax2 := 2;
                else
                    imax1 := 2; 
                    imax2 := 1; 
                end if; 
                max1 := candidatesL[imax1]; 
                max2 := candidatesL[imax2]; 
                for i := 3 to nbFe do 
                    lgth := candidatesL[i]; 
                    if lgth gt max1 then 
                        imax2 := imax1; 
                        max2 := max1; 
                        imax1 := i; 
                        max1 := lgth; 
                    elif lgth gt max2 then 
                        imax2 := i; 
                        max2 := lgth; 
                    end if; 
                end for;

                E[edge][3] := {candidates[imax1],candidates[imax2]}; 
            end if; 
        end if; 
    end for; 
end procedure; 

/*
    INPUT
    F : a reference to the faces of the polyhedron
    FE : a reference to the finite edges of the polyhedron
    FE : a reference to the intinite edges of the polyhedron

    Removes the redundancy in the faces of the polyhedron.
*/
procedure EliminateFaces(~F, ~FE, ~IE) 
    setF := (&join[ e[3] : e in FE]) join (&join[ e[3] : e in IE]); 
    newF := SetToSequence(setF); 
    n := #newF; 
    indexF := [0 : f in F]; 
    for f := 1 to n do 
        indexF[newF[f]] := f; 
    end for; 
    F := [F[newF[f]] : f in [1..n]]; 
    for f := 1 to n do
        F[f]`Edges := {};
    end for;
    nfe := #FE; 
    for e := 1 to nfe do 
        FE[e][3] := {indexF[f] : f in FE[e][3]}; 
        for f in FE[e][3] do
            Include(~(F[f]`Edges), e);
        end for;
    end for; 
    nie := #IE; 
    for e := 1 to nie do 
        IE[e][3] := {indexF[f] : f in IE[e][3]}; 
    end for; 
end procedure; 

/*
    INPUT
    F : a reference to the faces of the polyhedron
    FE : a reference to the finite edges of the polyhedron
    FE : a reference to the intinite edges of the polyhedron
    S : a sphere
    start : the index of an edge going to be affected (optional, 0=none, currently unused)
    nbdel : a reference for storing the number of deleted edges before 'start' (used only with 'start')
    eps12 : a small real for handling approximation, 10^(-pr/2)
    eps13 : a small real for handling approximation, 10^(-pr/3)
    eps110 : a small real for handling approximation, 10^(-pr/10)

    Modifies the polyhedron, according to intersecting it with the exterior of the sphere S
*/
procedure UpdateExteriorDomain(~F, ~FE, ~IE, S, start, ~nbdel, eps12, eps13, eps110) 
    for f in F do 
        if SameSphere(f,S,eps12) then 
            nbdel := 0;
            return; 
        end if; 
    end for; 
    
    FP := {}; 
    nbdel0 := 0;
    EatEdges(~F, ~IE, S, ~FP, {}    , ~nbdel0, eps12, eps13); 
    if start ne 0 then
        EP := &join[F[f]`Edges : f in FP];
        sstart := Include(EP,start);
    else
        sstart := {};
    end if;
    EatEdges(~F, ~FE, S, ~FP, sstart, ~nbdel , eps12, eps13); 
    NFE, NIE := NewEdges(F, S, FP, eps12, eps13); 
    
    Append(~F,S); 
	
    EliminateMultipleEdges(~F, ~FE, NFE, 2, eps12, eps110);
	EliminateMultipleEdges(~F, ~IE, NIE, 1, eps12, eps110);
	
	EliminateFaces(~F, ~FE, ~IE);
end procedure;

intrinsic ExteriorDomain(L::SeqEnum : Precision := DefaultPrecision) -> SeqEnum, SeqEnum, SeqEnum
{
    Computes the faces, finite edges and infinite edges of the exterior domain defined by the sheres in L
}
	F := [];
	FE := [];
	IE := [];
	n := #L;

    eps12 := epsilon(1/2,Precision);
    eps13 := epsilon(1/3,Precision);
    eps110 := epsilon(1/10,Precision);
	
    nbdel := 0;

	for s := 1 to n do
		UpdateExteriorDomain(~F, ~FE, ~IE, L[s], 0, ~nbdel, eps12, eps13, eps110);
	end for;
	
	return F,FE,IE;
end intrinsic;




/*

intervals.m
basic functions for handling finite unions of intervals

intervals.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

/*
    INPUT
    L : a sequence representing intervals
    treshold : an integer

    OUTPUT
    a sequence representing a disjoint union of intervals, the set of points x such that there are at least treshold intervals from L covering x
*/
function MergeIntervals(L, treshold)//treshold = 1 -> union, treshold = #L/2 -> intersection
	error if #L mod 2 ne 0, "#L must be even.";
	n := #L div 2;
	L2 := [<L[2*i-1],1> : i in [1..n]] cat [<L[2*i],-1> : i in [1..n]];
	Sort(~L2);
	L3 := [];
	count := 0;
	flag := false;
	N := 2*n;
	for i := 1 to N do
		count +:= L2[i][2];
		if count ge treshold xor flag then
			flag := not flag;
			Append(~L3,L2[i][1]);
		end if;
	end for;
	return L3;
end function;

function UnionIntervals(L)
	return MergeIntervals(L,1);
end function;

function IntersectionIntervals(L)
	return MergeIntervals(L,#L div 2);
end function;

function IntersectionCompacts(Li, B) //The compacts must be in normal form. If not, apply UnionIntervals.
	k := #Li;
	if k ne 0 then
		return MergeIntervals(&cat Li, k); //does not control whether every given interval is inside [0,B].
	else //an empty intersection returns the full interval [0,B];
		return [0*B,B];
	end if;
end function;

procedure ComplementInterval(~L, B) //complement in [0,B]
	n := #L;
	R := Parent(B);
	if n eq 0 then
		L := [R!0,B];
	else
		if L[n] eq B then
			Prune(~L);
		else
			Append(~L,B);
		end if;
		if L[1] eq R!0 then
			Exclude(~L,R!0);
		else
			Insert(~L,1,R!0);
		end if;
	end if;
end procedure;

function LengthInterval(L)
	n := #L div 2;
	if n eq 0 then
		return 0;
	else
        s := Parent(L[1])!0;
        maxi := 2*n;
        for i := 1 to maxi by 2 do
            s +:= L[i+1]-L[i];
        end for;
        return s;
	end if;
end function;

function PointInInterval(L)
	R := Parent(L[1]);
	pi2 := 2*Pi(R);
	n := #L;
	if L[1] eq 0 and L[n] eq pi2 then
		theta := (L[n-1]+L[2]+pi2)/2;
		if theta ge pi2 then
			theta -:= pi2;
		end if;
		return theta;
	else
		return (L[1]+L[2])/2;
	end if;
end function;

function IsInInterval(L, x)
	n := #L;
	error if n mod 2 ne 0, "#L must be even";
	
	if x lt L[1] then return false; end if;
	if x ge L[n-1] then return x le L[n]; end if;
	
	i := 1;
	j := n div 2;
	while i+1 lt j do
		k := (i+j) div 2;
		if x lt L[2*k-1] then
			j := k;
		else // x ge L[2*k-1]
			i := k;
		end if;
	end while;
	return x le L[2*i];
end function;






/*

properties.m
procedures for computing geometric properties of a Kleinian group

properties.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../kleinian.m" : isscalar, kleinianmatrix, displacement;
import "basics.m" : Distance, EndPoints, action;
import "../aux.m" : epsilon;

function polyrad(edges) //assumes that the polyhedron is bounded.
    zero := Parent(edges[1][1]`Center)!0;
    rad := Max([Max([Distance(zero,x) : x in EndPoints(e)]) : e in edges]);
    return rad;
end function;

intrinsic Radius(Edges :: SeqEnum) -> FldReElt
{
    The radius of the smallest hyperbolic ball centered at 0 containing the compact polyhedron with sequence of edges Edges.
}
    return polyrad(Edges);
end intrinsic;

procedure elimdup(~L, i, eps)
    isunique := true;
    for step in {-1,1} do
        j := i+step;
        while isunique and j ge 1 and j le #L and Abs(L[j][1]-L[i][1]) le eps do
            if isscalar(L[j][2]/L[i][2]) then
                isunique := false;
            end if;
            j +:= step;
        end while;
    end for;
    if not isunique then
        Remove(~L, i);
    end if;
end procedure;

procedure dichoinsert(~L, x, eps)
    a := 0;
    b := #L+1;
    while b-a gt 1 do
        c := (a+b) div 2;
        if x[1] lt L[c][1] then
            b := c;
        else
            a := c;
        end if;
    end while;
    Insert(~L, b, x);
    elimdup(~L, b, eps);
end procedure;

intrinsic Systole(faces :: SeqEnum, edges :: SeqEnum) -> FldReElt
{
    The minimum displacement of a loxodromic element in a Kleinian group, given the faces and edges of its Dirichlet domain.
}
    pr := Precision(faces[1]`Center[3]);
    eps := epsilon(1/10, pr);
    zero := Parent(edges[1][1]`Center)!0;
    rad := polyrad(edges) + eps;
    muls := [f`g : f in faces];
    L := [<Distance(zero, action(f`Matrix, zero)), f`g> : f in faces];
    Sort(~L);
    systol := -1;

    //hope the systole is among those
    for x in L do
        lg := x[1];
        g := x[2];
        depl := displacement(g,pr);
        if depl gt eps and (systol eq -1 or depl lt systol) then
            systol := depl;
        end if;
    end for;

    while systol eq -1 or #L ne 0 do

        vprint Kleinian, 3 : "#L", #L, "\tsystole", RealField(6)!systol;

        lg := L[1][1];
        g := L[1][2];
        Remove(~L, 1);

        depl := displacement(g,pr);
        if depl gt eps and (systol eq -1 or depl lt systol) then
            systol := depl;
        end if;

        for m in muls do
            mg := m*g;
            lmg := Distance(zero, action(kleinianmatrix(mg),zero));
            if lmg gt lg and (systol eq -1 or lmg le 2*rad+systol) then
                dichoinsert(~L, <lmg,mg>, eps);
            end if;
        end for;
    end while;
    return systol;
end intrinsic;



/*

random.m
functions for generating various random objects

random.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : Hdef;
import "volumes.m" : VolumeDisc, VolumeBall, dVolumeBall;
import "basics.m" : PointInCircle;
import "intervals.m" : LengthInterval;

function RandomReal(r)
 R := Parent(r);
 pr := Precision(R);
 return R!(Random(Floor(r*10^pr))*10^(-pr));
end function;

function RandomInInterval(I)
len := LengthInterval(I);
x := RandomReal(len);
k := 1;
ni := #I;
while 2*k+1 le ni and x+I[2*k-1] gt I[2*k] do
    x -:= I[2*k]-I[2*k-1];
    k +:= 1;
end while;
return x+I[2*k-1];
end function;

function RandomInCircle2(R)
 repeat
  x := 2*RandomReal(R!1)-1;
  y := 2*RandomReal(R!1)-1;
  w := x^2 + y^2;
 until w le 1;
 w := Sqrt(w);
 return [x/w,y/w];
end function;

function RandomInSphere(R)
 repeat
  x := 2*RandomReal(R!1)-1;
  y := 2*RandomReal(R!1)-1;
  z := 2*RandomReal(R!1)-1;
  w := x^2 + y^2 + z^2;
 until w le 1;
 w := Sqrt(w);
 return [x/w,y/w,z/w];
end function;

/*
    The (hyperbolic) radius of the (hyperbolic) disc of (hyperbolic) area v
*/
function RadiusDisc(v)
 R := Parent(v);
 return Argcosh(1+v/(2*Pi(R)));
end function;

/*
    An approximation of the (hyperbolic) radius of the (hyperbolic) ball of (hyperbolic) volume v 
*/
function ApproxRadiusBall(v)
 R := Parent(v);
 return Max(Log(2*v/Pi(R))/2,R!1/10);
end function;

/*
    The (hyperbolic) radius of the (hyperbolic) ball of (hyperbolic) volume v 
*/
function RadiusBall(v,eps)
 veps := v*eps;
 if v le eps then
  return (3*v/(4*Pi(Parent(v))))^(1/3);
 end if;
 r := ApproxRadiusBall(v);
 repeat
  diffe := VolumeBall(r)-v;
  r := r - diffe/dVolumeBall(r);
 until Abs(diffe) lt veps;
 return r;
end function;

/*
    Returns a random point in the (hyperbolic) disc of radius r, with distribution law given by the hyperbolic area
*/
function RandomHyperbolicDisc(H,r)
 R := BaseField(H);
 v := RandomReal(VolumeDisc(R!r));
 w := RandomInCircle2(R);
 rh := RadiusDisc(v);
 chrh := Cosh(rh);
 re := Sqrt((chrh-1)/(chrh+1));
 return re*(w[1]*H.2+w[2]*One(H));
end function;

/*
    Returns a random point in the (hyperbolic) ball of radius r, with distribution law given by the hyperbolic volume
*/
function RandomHyperbolicBall(H,r,eps)
 R := BaseField(H);
 v := RandomReal(VolumeBall(R!r));
 w := RandomInSphere(R);
 rh := RadiusBall(v,eps);
 chrh := Cosh(rh);
 re := Sqrt((chrh-1)/(chrh+1));
 return re*(w[1]*H.1+w[2]*H.2+w[3]*One(H));
end function;

function RandomQuatIJ( : H := Hdef)
	_,i,j := Explode(Basis(H));
	return Random((200)-100)/100 +  (Random(200)-100)/100*i + (Random(200)-100)/100*j;
end function;

//un peu obsolete avec RandomHyperbolicBall, mais pas la même loi...
function RandomInUnitBall( : H := Hdef)
	_,i,j := Explode(Basis(H));
	z := Random(10000) + Random(10000)*i + Random(10000)*j;
	n := 1 - 50/(50+Random(10000));
	z := z*n/Sqrt(Norm(z));
	return z;
end function;

function RandomInCircle(C)
	theta := Random(10000);
	return PointInCircle(C, theta);
end function;

function randprod(L)
    rid := Random(L);
    while Random(5) eq 0 do
        rid *:= Random(L);
    end while;
    return rid;
end function;




/*

volumes.m
functions for computing hyperbolic volumes and areas

volumes.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../aux.m" : epsilon;
import "basics.m" : sqrnorm, scalar, PointsToSphere, PerturbatedBtoH, IntersectionAngle, EndPoints;

function VolumeDisc(r)
 R := Parent(r);
 return 2*Pi(R)*(Cosh(r)-1);
end function;

function VolumeBall(r)
 R := Parent(r);
 return Pi(R)*(Sinh(2*r)-2*r);
end function;

function dVolumeBall(r)
 R := Parent(r);
 return 2*Pi(R)*(Cosh(2*r)-1);
end function;

/*
    Precomputes the coefficients of the power series expansion of the Lobachevsky function. Computes as many coefficients as required for precision pr
*/
function ComputeZetas(pr)
	vprint Kleinian: "precomputing zeta values";
	zeta := RiemannZeta( : Precision := pr);
	Nzeta := Floor(pr/Log(10,4))+1;
	zetas := [(Evaluate(zeta, 2*n))/(n*(2*n+1)) : n in [1..Nzeta]];
    return zetas;
end function;

function Lobachevsky(x, zetas)
	R := Parent(zetas[1]);
	pr := Precision(zetas[1]);
	pi := Pi(R);

	if x lt 0 then
		return -Lobachevsky(-x, zetas);
	elif x ge pi then
		return Lobachevsky(x-Floor(x/pi)*pi, zetas);
	elif x gt pi/2 then
		return -Lobachevsky(pi-x, zetas);
	elif x eq 0 then
		return 0;
	else
		value := R!0;
		N := Floor(pr/Log(10,4))+1;

		quo := x / pi;
		quo2 := quo^2;
		invquo2 := 1/quo2;
		logquo := Log(10,invquo2);
		N := Floor( (pr + Log(10, 2/3) - Log(10, 1 - quo2))/logquo );

		for n:=N to 1 by -1 do
			value +:= zetas[n];
			value *:= quo2;
		end for;
		value *:= x;
		value +:= x - x*Log(2*x);

		return value;
	end if;
end function;

function StandardParametersVolume(alpha, gamma, zetas)
	R := Parent(zetas[1]);
	hpi := Pi(R)/2;
	return 1/4*(Lobachevsky(alpha+gamma,zetas) + Lobachevsky(alpha-gamma,zetas) + 2*Lobachevsky(hpi-alpha, zetas));
end function;

function StandardTetrahedronVolume(y,z,zetas,eps12) //x=0, y,z in C, OBC = pi/2, sqrnorm(y,z)<=1, tetrahedron based on unit hemisphere with one vertex at infinity.
	dist := Abs(y-z);
	R := Parent(zetas[1]);
	pr := Precision(R);
	if Abs(z) le eps12 or dist le eps12 then return R!0; end if;
	cosalpha := Abs(y)/Abs(z);
	cosgamma := Abs(y);
    if cosalpha ge 1 then
        alpha := 0*eps12;
    else
    	alpha := Arccos(cosalpha);
    end if;
	gamma := Arccos(cosgamma);
	return StandardParametersVolume(alpha, gamma, zetas);
end function;

function NormalizedCenteredTetrahedronVolume(y,z,zetas,eps12) //x=0, y,z in C, sqrnorm(y,z)<=1, tetrahedron based on unit hemisphere with one vertex at infinity.
	N := Norm(z-y);
	R := Parent(zetas[1]);
	pr := Precision(R);
	if N lt eps12 then return R!0; end if;
	t := -Re(y*Conjugate(z-y))/N;
	D := y + t*(z-y);
	return Abs( Sign(Im(D*Conjugate(z)))*StandardTetrahedronVolume(D,z, zetas, eps12) + Sign(Im(y*Conjugate(D)))*StandardTetrahedronVolume(D,y, zetas,eps12) );
end function;

function NormalizedTetrahedronVolume(x,y,z, zetas, eps12) //x,y,z in C, sqrnorm(x,y,z)<=1, tetrahedron based on unit hemisphere with one vertex at infinity.
	return Abs( Sign(Im(y*Conjugate(z)))*NormalizedCenteredTetrahedronVolume(y,z,zetas,eps12) + Sign(Im(x*Conjugate(y)))*NormalizedCenteredTetrahedronVolume(x,y, zetas,eps12) + Sign(Im(z*Conjugate(x)))*NormalizedCenteredTetrahedronVolume(x,z, zetas,eps12) );
end function;

function InfinityVertexTetrahedronVolume(x,y,z, zetas,eps12) //x,y,z in H^3, tetrahedron with one vertex at infinity
	R := Parent(zetas[1]);
	C<I> := ComplexField(R);
	s := PointsToSphere(x,y,z);
	if s`Radius eq 0 then return 0; end if; //un epsilon ?
	X := (x-s`Center)/s`Radius;
	Y := (y-s`Center)/s`Radius;
	Z := (z-s`Center)/s`Radius;
	return NormalizedTetrahedronVolume(C!X[1]+I*X[2], C!Y[1]+I*Y[2], C!Z[1]+I*Z[2], zetas, eps12);
end function;

function SemiIdealTetrahedronVolume(X,Y,Z,v,zetas,eps12) //X,Y,Z in H^3, one vertex v in C (represented in R+Ri subset H)
	R := Parent(zetas[1]);
	if Norm(X-v) le eps12 or Norm(Y-v) le eps12 or Norm(Z-v) le eps12 then
		return R!0;
	end if;
	return InfinityVertexTetrahedronVolume(1/(v-X), 1/(v-Y), 1/(v-Z), zetas, eps12);
end function;

//passer en function ?
intrinsic InfinityEnd(X :: AlgQuatElt, Y :: AlgQuatElt) -> AlgQuatElt, AlgQuatElt //the ends on the sphere at infinity of the geodesic between x and y
{}
	x := X;
	x[3] := 0;
	y := Y;
	y[3] := 0;
	
	alpha := (sqrnorm(X)-sqrnorm(Y) + 2*(sqrnorm(y)-scalar(x,y)))/sqrnorm(x-y);
	beta := (sqrnorm(Y)-sqrnorm(X) + 2*(sqrnorm(x)-scalar(x,y)))/sqrnorm(x-y);
	
	S := alpha*x + beta*y;
	P := scalar(S,(x+y)/2) - (sqrnorm(X)+sqrnorm(Y))/2;
	delta := sqrnorm(S)/4-P;
	r := Sqrt(delta);
	u := (y-x)/Sqrt(sqrnorm(y-x));
	return S/2+r*u, S/2-r*u;
end intrinsic;

function TetrahedronVolume(X,Y,Z,V,zetas,eps12) //x,y,z,v in H^3
	R := Parent(zetas[1]);
	if Norm(X-Y) le eps12 or Norm(X-Z) le eps12 or Norm(X-V) le eps12 or Norm(Y-Z) le eps12 or Norm(Y-V) le eps12 or Norm(Z-V) le eps12 then
		return R!0;
	end if;
	v := InfinityEnd(X,V);
	vol := SemiIdealTetrahedronVolume(X,Y,Z,v,zetas,eps12) - SemiIdealTetrahedronVolume(V,Y,Z,v,zetas,eps12);
    return vol;
end function;

function PolyhedronVolume(F, E, zetas) //F : faces, E : edges.
	H<i,j,k> := Parent(F[1]`Center);
    R := BaseField(H);
    eps12 := epsilon(1/2, Precision(R));
	
	EdgesOfFace := [[] : f in F];
	m := #E;
	for e := 1 to m do
		for f in E[e][3] do
			Append(~EdgesOfFace[f], EndPoints(E[e]));
		end for;
	end for;
	
	TetrahedraVertices := [];
	n := #F;
	for f := 1 to n do
		x0 := Rep(EdgesOfFace[f][1]);
		for ep in EdgesOfFace[f] do
			Append(~TetrahedraVertices, [PerturbatedBtoH(j,x0)] cat [PerturbatedBtoH(j,w) : w in ep]);
		end for;
	end for;
	
	x00 := Rep(EdgesOfFace[1][1]);
	x00 := PerturbatedBtoH(j,x00);
    vol := R!0;
    for t in TetrahedraVertices do
        volt := TetrahedronVolume(t[1],t[2],t[3],x00,zetas,eps12);
        vol +:= volt;
    end for;
    return vol;
end function;

function PolyhedronArea(F,E)
	R := Parent(F[1]`Radius);
	pi := Pi(R);
    ar := R!0;
    for e in E do
        fe := SetToSequence(e[3]);
        ar -:= IntersectionAngle(F[fe[1]],F[fe[2]]);
    end for;
    ar +:= (#F-2)*pi;
    return ar;
end function;



/*

maple.m
Functions for producing Maple code drawing fundamental domains

maple.m is part of KleinianGroups, version 1.0 of September 25, 2012.
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/
import "../geometry/intervals.m" : PointInInterval;
import "../geometry/basics.m" : PointInCircle, Sphere, Circle;
import "../kleinian.m" : Hdef, Rdef, Jdef, Idef;

intrinsic MapleReal(a::FldReElt) -> MonStgElt
{Returns 'a' as a string}
	R := RealField(10);
	if a gt 0 then
		return Sprint(R!a);
	else
		return "("*Sprint(R!a)*")";
	end if;
end intrinsic;

intrinsic MapleCoordinates(x::AlgQuatElt) -> MonStgElt
{Returns the coordinates of x as a string}
	Co := Coordinates(x);
	return MapleReal(Co[1]) * "," * MapleReal(Co[2]) * "," * MapleReal(Co[3]);
end intrinsic;

intrinsic MaplePoint(x::AlgQuatElt) -> MonStgElt
{Returns the Maple command to plot x}
	return "point([" * MapleCoordinates(x) * "],symbol=solidsphere,color=blue)";//or cross ?
end intrinsic;

intrinsic MapleCaption(Cap::MonStgElt, x::AlgQuatElt) -> MonStgElt
{Returns the Maple command to plot the string Cap at the position x}
	return "textplot3d([" * MapleCoordinates(x) * ",\"" * Cap * "\"],symbol=solidsphere,color=blue)";
end intrinsic;

intrinsic MapleEdgeCaption(E::Tup, n::RngIntElt) -> MonStgElt
{Returns the Maple command to plot the number n in the middle of the edge E}
	theta := PointInInterval(E[2]);
	x := PointInCircle(E[1], theta);
	return MapleCaption(Sprint(n),x);
end intrinsic;

intrinsic MapleSphere(S::Rec : Transparency := 67 , Grid := false) -> MonStgElt
{Returns the Maple command to plot S}
	if Grid then
		return "sphere([" * MapleCoordinates(S`Center) * "]," * MapleReal(S`Radius) * ",transparency=" * IntegerToString(Transparency) * "*0.01)";
	else
		return "sphere([" * MapleCoordinates(S`Center) * "]," * MapleReal(S`Radius) * ",transparency=" * IntegerToString(Transparency) * "*0.01,style=patchnogrid)";
	end if;
end intrinsic;

intrinsic MapleCircle(C::Rec : Interval := [0.,2*Pi(RealField())], Dash := false, Color := "red") -> SeqEnum[MonStgElt]
{Returns the Maple command to plot C}
	H<i,j,k> := Parent(C`e3);
	x1 := C`e1;
	x2 := C`e2;
	Co := Coordinates(C`Center);
	Rad := MapleReal(C`Radius);
	
	n := #Interval;
	m := n div 2;
	
	if Dash then
		Sdash := ",linestyle=dot";
	else
		Sdash := "";
	end if;
	
	return ["spacecurve([" 
		* MapleReal(Co[1]) * "+" * Rad * "*cos(t)*" * MapleReal(x1[1]) * "+" * Rad * "*sin(t)*" * MapleReal(x2[1]) * "," 
		* MapleReal(Co[2]) * "+" * Rad * "*cos(t)*" * MapleReal(x1[2]) * "+" * Rad * "*sin(t)*" * MapleReal(x2[2]) * ","
		* MapleReal(Co[3]) * "+" * Rad * "*cos(t)*" * MapleReal(x1[3]) * "+" * Rad * "*sin(t)*" * MapleReal(x2[3])
		* "],t=" * MapleReal(Interval[2*i-1]) * ".." * MapleReal(Interval[2*i]) * ",thickness=1,color="* Color * Sdash * ")" : i in [1..m]];
end intrinsic;

intrinsic MapleExteriorDomain(F::SeqEnum, FE::SeqEnum, IE::SeqEnum : Caption := false, Sphere := false) -> SeqEnum[MonStgElt]
{Returns the Maple command to plot the exterior domain with faces F, finite edges FE, infinite edges IE}
	nfe := #FE;
	nie := #IE;
	if Caption then
		S := [MapleEdgeCaption(FE[e],e) : e in [1..nfe]] cat [MapleEdgeCaption(IE[e],e) : e in [1..nie]];
	else
		S := [];
	end if;
	if Sphere then
	  UnitSphere := Sphere(Hdef!0, 1.);
	  sph := [MapleSphere(UnitSphere : Transparency := 100, Grid := true)];
	else
	  sph := &cat[MapleCircle(Circle(Hdef!0,Rdef!1,Hdef!1) : Color := "black"),MapleCircle(Circle(Hdef!0,Rdef!1,Idef) : Color := "black"),MapleCircle(Circle(Hdef!0,Rdef!1,Jdef) : Color := "black"), ["spacecurve([t,0,0], t=-1..1, thickness=1,color=black)","spacecurve([0,t,0], t=-1..1, thickness=1,color=black)","spacecurve([0,0,t], t=-1..1, thickness=1,color=black)"]];
	end if;
	
	return sph
		cat [MapleSphere(s : Transparency := 85) : s in F] 
		cat (&cat[MapleCircle(e[1] : Interval := e[2]) : e in FE cat IE])
		cat S;
end intrinsic;

intrinsic MapleDraw(s::SeqEnum[MonStgElt] : view := 0) -> MonStgElt
{Returns the Maple command to display the plots defined by the commands of the sequence s}
	Str := "with(plottools): with(plots): s:=";
	tail := "";
	if not IsEmpty(s) then
		tail := Reverse(s)[1];
		prune := Prune(s);
		for x in prune do
			Str := Str * x * ",";
		end for;
	end if;
	if view eq 0 then
		V := "";
	else
		a := MapleReal(view);
		V := ",view=[-" * a * ".." * a * "," * "-" * a * ".." * a * "," * "-" * a * ".." * a * "]";
	end if;
	return Str * tail * ": display(s,scaling=constrained" * V * ");";
end intrinsic;

intrinsic MapleFile(s::MonStgElt, file::MonStgElt)
{Create a Maple input file "file.mpl" which contains the commands s}
	F := Open(file*".mpl", "w");
	Put(F,s);
	Flush(F);
end intrinsic;



