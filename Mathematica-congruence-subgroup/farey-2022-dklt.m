/*

farey-2022-dklt.m
*/


s := FareySymbol(Gamma0(n));



SetOutputFile("farey-2022-cusps.txt":Overwrite := true);
print Cusps(s);
UnsetOutputFile();
SetOutputFile("farey-2022-generators.txt":Overwrite := true);
print Generators(s);
UnsetOutputFile();
quit;
