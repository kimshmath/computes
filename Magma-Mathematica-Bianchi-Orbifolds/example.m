/*

example.m
An example of use of the package KleinianGroups

example.m is part of KleinianGroups, version 1.0 of September 25, 2012
KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with KleinianGroups, in the file COPYING.  If not, see <http://www.gnu.org/licenses/>.

*/

AttachSpec("klngpspec");
SetVerbose("Kleinian", 0);

_<x> := PolynomialRing(Rationals());
F<t> := NumberField(x^3-x+1);
ZF := Integers(F);

D := Factorization(5*ZF)[1][1];
B := QuaternionAlgebra(D, RealPlaces(F));
O := MaximalOrder(B);

//Computation of the norm one group


//precomputation, common to every group (with the same precision) : useful for intensive computations
import "geometry/volumes.m" : ComputeZetas;
print "precomputing coefficients...";
zetas := ComputeZetas(100); 
print "...done.\n\n";


//Computation of the maximal commensurable group


//Computations with a Bianchi group
O := BianchiOrder(29);
_, Faces, Edges := NormalizedBasis(O : zetas := zetas);
PG, PGenerators := Presentation(Faces, Edges, O);
print "H_1(PSL2(O_-29), Z) :", AbelianQuotient(PG);
G,Generators := LiftPresentation(PG, PGenerators, O, true);
print "H_1(SL2(O_-29), Z) :", AbelianQuotient(G);

import "bianchi.m" : QuatToMatrix;
print "generators of SL2(O_-29) :", [QuatToMatrix(g) : g in Generators], "\n\n";

