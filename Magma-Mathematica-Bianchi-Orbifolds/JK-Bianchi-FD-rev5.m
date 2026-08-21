/*

JK-Bianchi-H1.m

Find a (small) list of generators in \Gamma_d which spans H1(\Gamma_d).

* JK-Bianchi-H1.m, JK-Bianchi-H1.nb and Page's package should be in the same folder

1. Run H1Bianchi.nb in Mathematica
2. An output will be written as "JK-Bianchi-H1-out-gen-psl-matrices.txt".

*/

SetOutputFile("JK-Bianchi-FD-out-errors.txt":Overwrite := true);

AttachSpec("klngpspec");
SetVerbose("Kleinian", 0);



//Computation of the norm one group


//precomputation, common to every group (with the same precision) : useful for intensive computations
import "geometry/volumes.m" : ComputeZetas;
print "precomputing coefficients...";
zetas := ComputeZetas(100); 
print "...done.\n\n";


O := BianchiOrder(d);
Basis, Faces, Edges := NormalizedBasis(O : zetas := zetas);
PG, PGenerators := Presentation(Faces, Edges, O);
H1PG, H1f := AbelianQuotient(PG);
HPG, Hf := FreeAbelianQuotient(H1PG);


dimsrc := NumberOfGenerators(PG);
dimtar := NumberOfGenerators(HPG);
UnsetOutputFile();


SetOutputFile("JK-Bianchi-FD-out-N-pi1-gen.txt":Overwrite := true);
print(dimsrc);
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-out-N-H1-gen.txt":Overwrite := true);
print(dimtar);
UnsetOutputFile();




SetOutputFile("JK-Bianchi-FD-Basis-raw.txt":Overwrite := true);
print(Basis);
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-Faces-raw.txt":Overwrite := true);
print(Faces);
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-Edges-raw.txt":Overwrite := true);
print(Edges);
UnsetOutputFile();


SetOutputFile("JK-Bianchi-FD-out-errors.txt":Overwrite := false);

if NumberOfGenerators(H1PG) eq dimtar then
	HPG, Hg := AbelianQuotient(PG);
else
	Hg := H1f * Hf;
end if;
UnsetOutputFile();


SetOutputFile("JK-Bianchi-FD-out-quotients.txt":Overwrite := true);
for i in [1..dimsrc] do 
		print Hg(PG.i);
end for;
UnsetOutputFile();


import "bianchi.m" : QuatToMatrix;

SetOutputFile("JK-Bianchi-FD-out-psl-matrices.txt":Overwrite := true);
print "{";
for i in [1..#Faces] do 
		m := QuatToMatrix(Faces[i]`g);
		if i lt #Faces then
			print "{{",m[1,1], ",",m[1,2],"},{",m[2,1],",",m[2,2],"}},";
		else print "{{",m[1,1], ",",m[1,2],"},{",m[2,1],",",m[2,2],"}}}";
		end if;	
end for;
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-out-quat-g.txt":Overwrite := true);
print "{";
for i in [1..#Faces] do 
		if i lt #Faces then
				print "{",Faces[i]`g,"},";
		else 	print "{",Faces[i]`g,"}}";
		end if;	
end for;
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-out-Edges.txt":Overwrite := true);
print "{";
for i in [1..#Edges] do 
		c := Edges[i][1]`Center;
		r := Edges[i][1]`Radius;
		e1 := Edges[i][1]`e1;
		e2 := Edges[i][1]`e2;
		e3 := Edges[i][1]`e3;
		if #Edges[i][2] eq 2 then
			ang1 := Edges[i][2][1];
			ang2 := Edges[i][2][2];
		else 
			ang1 := Edges[i][2][3];
			ang2 := Edges[i][2][2];
		nbfaces := Edges[i][3];
		end if;
		if i lt #Edges then
			print "{",c, ",",r,",",e1,",",e2,",",e3,",",ang1,",",ang2,"},";
		else print "{",c, ",",r,",",e1,",",e2,",",e3,",",ang1,",",ang2,"}}";
		end if;
end for;
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-out-Edges-nbfaces.txt":Overwrite := true);
print "{";
for i in [1..#Edges] do 
		nbfaces := Edges[i][3];
		if i lt #Edges then
			print nbfaces,",";
		else print nbfaces,"}";
		end if;
end for;
UnsetOutputFile();


SetOutputFile("JK-Bianchi-FD-out-Faces.txt":Overwrite := true);
print "{";
for i in [1..#Faces] do 
		c := Faces[i]`Center;
		r := Faces[i]`Radius;
		e := Faces[i]`Edges;
		if i lt #Faces then
			print "{",c, ",",r,",",e,"},";
		else print "{",c, ",",r,",",e,"}}";
		end if;
end for;
UnsetOutputFile();

SetOutputFile("JK-Bianchi-FD-out-Faces-nbedges.txt":Overwrite := true);
print "{";
for i in [1..#Faces] do 
		nbedges := Faces[i]`Edges;
		if i lt #Faces then
			print nbedges,",";
		else print nbedges,"}";
		end if;
end for;
UnsetOutputFile();

quit;
