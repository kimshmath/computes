R<x> := PolynomialRing(Rationals());
D := 7;
K := NumberField(x^2+D);
Evaluate(LSeries(K),2) * D^(3/2)/(2*Pi(RealField()))^2;