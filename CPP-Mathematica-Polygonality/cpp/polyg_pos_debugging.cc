//	Positive-Polygonality Checker
//	Sang-hyun (Sam) Kim (c) 2010
// 		
//	Note. 
//	If the length considered is larger than 15, change length,length2,length4 properly
//
// 	This program checks the positive-polygonality for the minimal, diskbusting sets 
//	of words with a given length in F_2; this means, we also require that each corner at a denser vertex occurs at most once.
//	moreover, proven cases (regular or positive) are excluded.
//	
//
// 	GNU LP solver library is needed.
// 	To install glpk:
/*
cd
mkdir $HOME/glpk
gzip -d glpk-4.43.tar.gz
tar -x < glpk-4.43.tar
cd glpk-4.43
./configure --prefix=$HOME/glpk
make
make check
make install
cd $HOME/glpk/lib
rm *.so

When compiling:
g++ -I$HOME/glpk/include -c polyg_pos.cc
g++ -L$HOME/glpk/lib -o polyg_pos.exe polyg_pos.o -lglpk -lm

OR, 
icc -Kc++ -I$HOME/glpk/include -c polyg.cc
icc -Kc++ -L$HOME/glpk/lib -o polyg.out polyg.o -lglpk -lm 
./a.out < input.txt > output.txt
where input.txt contains the length (number only)

To find out (and kill, if necessary) PID of the job
ps aux | grep shkim

*/


#include <iostream>
#include <algorithm>
#include <math.h>
#include <glpk.h>

using namespace std;

#define length 14 	// max length of the words

//max. number of constraints expected
#define length2 200 // the number of pairs (at a's and b's)

//max. number of variables expected
#define length4 200	// the number of simple cycles never exceeds 200 if length <= 15

#define  REAL  double
// maximum number of non-zero entries
#define MAXALL 5 * length4 + 1 
// each column contains at most 5 (including the last row, which is 1) non-zero entries
// + 1 as we count from ar[1]... disregarding ar[0].

// return the position of the pair (i,j) in 12, 13, 23, 14, 24, ... order
inline int PairPosition (int i, int j){ return (max(i,j) - 1) * (max(i,j) - 2) / 2 + min(i,j); }

int checkpolygonality (int l)
{
	int stat, p,pp,q,r,i,j, ii,jj, iatmp1, iatmp2, dega, degb, elemcount,PairA,PairB,RowN, SCN,SCCount, solnfound1, solnfound2;
	REAL ar[MAXALL];
	int SCM[length2][length4];
	int ia[MAXALL], ja[MAXALL];
	int sigma[length], tau[length];
	glp_prob *lp;
	glp_iocp parm;
	glp_init_iocp(&parm);
	parm.msg_lev = GLP_MSG_OFF;
//	parm.fp_heur = GLP_ON;
	int count = 0;
	glp_smcp parmsmcp;
	glp_init_smcp(&parmsmcp);
	parmsmcp.msg_lev = GLP_MSG_OFF;
	
	for (r = 1; r <= l/2.0; r++)
		for (q = r; q <= l/2.0 -r; q++)
			for ( pp = 0; pp < l / 2.0 - q - r; pp++){
				p = l - pp - 2 * q - 2 * r;
				if (q - r > pp) continue; // check the minimality of the graph
				cout << "Checking (p,pp,q,r) = (" << p << ", " << pp << ", " << q << ", " << r << ")\n";
				PairA = (p + q + r) * (p + q + r - 1) / 2;
				PairB = (pp + q + r) * (pp + q + r - 1) / 2;
				RowN = PairA + PairB + 1;
				SCN = p * (p - 1) / 2 + pp * (pp - 1) / 2 + q * (q - 1) + r * (r - 1) 
					+ p * pp * q * q + p * pp * r * r + q * q * r * r +  2 * (p + pp) * q * r;
				dega = p + q + r; degb = pp + q + r;	 
				
				for (i = 1; i <= dega; i++) sigma[i] = i;	// initialize permutations
				do {
					for (i = 1; i <= degb; i++) tau[i] = i;
					do {
						SCCount = 1;
						elemcount = 1;						
						// if the last r numbers of tau are not increasing, check is redundant						
						if (r > 1) {
							for (i = 1; i < r; i++)
								if (tau[degb - r + i] > tau[degb - r + i + 1]) goto next;
						}
						
						// Add bigon rows joining a+-
						for (i = 1; i < p; i++)
							for (j = i + 1; j <= p; j++){
								iatmp1 = PairPosition(i,j);
								iatmp2 = PairPosition(sigma[i],sigma[j]);
								if (iatmp1==iatmp2) goto next;
								ia[elemcount] = iatmp1 + RowN;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								ia[elemcount] = iatmp2;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = -1;
							}
							
						// Add bigon rows joining b + -
						for (i = 1; i < pp; i++)
							for (j = i + 1; j <= pp; j++){
								iatmp1 = PairPosition(i,j);
								iatmp2 = PairPosition(tau[i],tau[j]);
								if (iatmp1==iatmp2) goto next;								
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								ia[elemcount] = iatmp2 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = -1;	
							}


						// Add bigon rows joining a + b + 
						for (i = p + q + 1; i < p + q + r; i++)
							for (j = i + 1; j <= p + q + r; j++){
								iatmp1 = PairPosition(i,j);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								ia[elemcount] = iatmp1 + RowN;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								
								iatmp1 = PairPosition(i + pp - p, j + pp - p);		
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = 1;
							}

						// Add bigon rows joining a - b - 
						for (i = p + q + 1; i < p + q + r; i++)
							for (j = i + 1; j <= p + q + r; j++){
								iatmp1 = PairPosition(sigma[i],sigma[j]);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = -1;
								iatmp1 = PairPosition(tau[i+pp-p],tau[j+pp-p]);
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = -1;
							}

						// Add bigon rows joining a - b + 
						for (i = pp + 1; i < pp + q; i++)
							for (j = i + 1; j <= pp + q; j++){
								iatmp1 = PairPosition(sigma[pp+p+q-i+1],sigma[pp+p+q-j+1]);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = -1;
								iatmp1 = PairPosition(i,j);
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = 1;
							}

						// Add bigon rows joining a + b -
						for (i = p + 1; i < p + q; i++)
							for (j = i + 1; j <= p + q; j++){
								iatmp1 = PairPosition(i,j);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								ia[elemcount] = iatmp1 + RowN;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								
								iatmp1 = PairPosition(tau[pp+p+q-i+1],tau[pp+p+q-j+1]);
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = -1;
							}

						// Add square rows joining a + a - b - b + 
						for (i = 1; i <= p; i++)
							for(j = p + q + 1; j <= p + q + r; j++)
								for(ii = 1; ii <= pp; ii++)
									for(jj = p + q + 1; jj <= p + q + r; jj++){
										solnfound1 = 0;
										solnfound2 = 0;
										iatmp1 = PairPosition(i,j);	
										iatmp2 = PairPosition(sigma[i],sigma[jj]);
										if (iatmp1==iatmp2) solnfound1 = 1;
										else {
											ia[elemcount] = iatmp1;
											ja[elemcount] = SCCount;
											ar[elemcount++] = 1;
											ia[elemcount] = iatmp2;
											ja[elemcount] = SCCount;
											ar[elemcount++] = -1;
										}
										ia[elemcount] = iatmp1 + RowN;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
										
										iatmp1 = PairPosition(ii,j+pp-p);
										iatmp2 = PairPosition(tau[ii],tau[jj+pp-p]);
										if (iatmp1==iatmp2) solnfound2 = 1;
										else {
											ia[elemcount] = iatmp1 + PairA;
											ja[elemcount] = SCCount;
											ar[elemcount++] = 1;
											ia[elemcount] = iatmp2 + PairA;
											ja[elemcount] = SCCount;
											ar[elemcount++] = -1;
										}
										if (solnfound1 * solnfound2)  goto next;
										SCCount++;
									}
			
						// Add square rows joining a + b - a - b + 

						for(i = p + 1; i <= p + q; i++)
							for(j = p + q + 1; j <= p + q + r; j++)
								for(ii = pp + 1; ii <= pp + q; ii++)
									for(jj = p + q + 1; jj <= p + q + r; jj++){
										solnfound1 = 0;
										solnfound2 = 0;
										iatmp1 = PairPosition(i,j);	
										iatmp2 = PairPosition(sigma[jj],sigma[pp+p+q+1-ii]);
										if (iatmp1==iatmp2) solnfound1 = 1;
										else {
											ia[elemcount] = iatmp1;
											ja[elemcount] = SCCount;
											ar[elemcount++] = 1;
											ia[elemcount] = iatmp2;
											ja[elemcount] = SCCount;
											ar[elemcount++] = -1;
										}
										ia[elemcount] = iatmp1 + RowN;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
										
										iatmp1 = PairPosition(ii,j+pp-p);
										iatmp2 = PairPosition(tau[pp+p+q+1-i],tau[jj+pp-p]);
										if (iatmp1==iatmp2) solnfound2 = 1;
										else {
											ia[elemcount] = iatmp1 + PairA;
											ja[elemcount] = SCCount;
											ar[elemcount++] = 1;
											ia[elemcount] = iatmp2 + PairA;
											ja[elemcount] = SCCount;
											ar[elemcount++] = -1;
										}
										if (solnfound1 * solnfound2)  goto next;
										SCCount++;									
									}

						
						// Add square rows joining a + b - b + a - 			
						for(i = 1; i <= p; i++)
							for(j = p + 1; j <= p + q; j++)
								for(ii = 1; ii <= pp; ii++)
									for(jj = pp + 1; jj <= pp + q; jj++){
										solnfound1 = 0;
										solnfound2 = 0;
										iatmp1 = PairPosition(i,j);	
										iatmp2 = PairPosition(sigma[i],sigma[pp+p+q+1-jj]);
										if (iatmp1==iatmp2) solnfound1 = 1;										
										else {
											ia[elemcount] = iatmp1;
											ja[elemcount] = SCCount;
											ar[elemcount++] = 1;
											ia[elemcount] = iatmp2;
											ja[elemcount] = SCCount;
											ar[elemcount++] = -1;
										}
										ia[elemcount] = iatmp1 + RowN;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
										
										iatmp1 = PairPosition(ii,jj);
										iatmp2 = PairPosition(tau[pp+p+q+1-j],tau[ii]);
										if (iatmp1==iatmp2) solnfound2 = 1;
										else {
											ia[elemcount] = iatmp1 + PairA;
											ja[elemcount] = SCCount;
											ar[elemcount++] = 1;
											ia[elemcount] = iatmp2 + PairA;
											ja[elemcount] = SCCount;
											ar[elemcount++] = -1;
										}
										if (solnfound1 * solnfound2)  goto next;
										SCCount++;																			
									}
						
						// Add triangles joining a + b + a - 
						for(i = 1; i <= p; i++)
							for(j = p + q + 1; j <= p + q + r; j++)
								for(ii = pp + 1; ii <= pp + q; ii++){
									iatmp1 = PairPosition(ii,j+pp-p);					// pair at b+
									ia[elemcount] = iatmp1 + PairA;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									iatmp1 = PairPosition(i,j);							// pair at a+
									iatmp2 = PairPosition(sigma[i],sigma[pp+p+q-ii+1]); // pair at a-
									if (iatmp1!=iatmp2) {
										ia[elemcount] = iatmp1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
										ia[elemcount] = iatmp2;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}
									ia[elemcount] = iatmp1 + RowN;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									
									SCCount++;			
								}

						// Add triangles joining a+b+b- 
						for(i = p + 1; i <= p + q; i++)
						  for(j = p + q + 1; j <= p + q + r; j++)
						    for(ii = 1; ii <= pp; ii++){
								iatmp1 = PairPosition(i,j);							// pair at a+
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								
								ia[elemcount] = iatmp1 + RowN;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								
								iatmp1 = PairPosition(ii,j+pp-p);					// pair at b+
								iatmp2 = PairPosition(tau[ii],tau[pp+p+q+1-i]);	 	// pair at b-
								if (iatmp1!=iatmp2) {
									ia[elemcount] = iatmp1+PairA;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									ia[elemcount] = iatmp2+PairA;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;			
								}
								SCCount++;
							}	

						// Add triangles joining a+a-b- 
						for(i = 1; i <= p; i++)
						  for(j = p + 1; j <= p + q; j++)
						    for(ii = p + q + 1; ii <= p + q + r; ii++){
								iatmp1 = PairPosition(i,j);							// pair at a+
								iatmp2 = PairPosition(sigma[i],sigma[ii]); 			// pair at a-
								if (iatmp1!=iatmp2) {
									ia[elemcount] = iatmp1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									ia[elemcount] = iatmp2;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}
								ia[elemcount] = iatmp1 + RowN;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								
								iatmp2 = PairPosition(tau[ii+pp-p],tau[pp+p+q+1-j]);// pair at b-
								ia[elemcount] = iatmp2+PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = -1;
							}	


						// Add triangles joining a-b+b- 
						for(i = 1; i <= pp; i++)
						  for(j = pp + 1; j <= pp + q; j++)
						    for(ii = p + q + 1; ii <= p + q + r; ii++){
								iatmp2 = PairPosition(sigma[ii],sigma[pp+p+q+1-j]);
								ia[elemcount] = iatmp2;
								ja[elemcount] = SCCount;
								ar[elemcount++] = -1;							// pair at a-
								iatmp1 = PairPosition(i,j);						// pair at b+
								iatmp2 = PairPosition(tau[i],tau[ii+pp-p]);	 	// pair at b-
								if (iatmp1!=iatmp2) {
									ia[elemcount] = iatmp1+PairA;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									ia[elemcount] = iatmp2+PairA;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}
								SCCount++;
							}
						
						SCCount--;			// revert the last (extra) increment of Simple Cycle Counts
	
						// Add the last row consisting of 1's
						for (i = 1; i <= SCCount; i++){
							ia[elemcount] = RowN;
							ja[elemcount] = i;
							ar[elemcount++] = 1;
						}

						elemcount--;		// revert the last (extra) increment of non-zero entry counts
						lp = glp_create_prob();

						glp_set_obj_dir(lp, GLP_MIN);
						glp_add_rows(lp, RowN+PairA);
						for (i = 1; i < RowN; i++) glp_set_row_bnds(lp, i, GLP_FX, 0, 0);
						glp_set_row_bnds(lp, RowN, GLP_LO, 1, 0);
						for (i = RowN + 1; i <= RowN + PairA; i++) glp_set_row_bnds(lp, i, GLP_UP, 0, 1);
						glp_add_cols(lp, SCCount);
						for (j = 1; j <= SCCount; j++) {
							glp_set_col_bnds(lp, j, GLP_LO, 0, 0);
							glp_set_obj_coef(lp, j, 0);
						}
						for (j = 1; j <= SCCount; j++) glp_set_col_kind(lp, j, GLP_IV);
						glp_load_matrix(lp, elemcount, ia, ja, ar);
						glp_simplex(lp,&parmsmcp);
						glp_intopt(lp, &parm);
// debugging code
for (i = 1; i <= elemcount; i++) SCM[ia[i]][ja[i]] = ar[i];
// print the matrix computed so far
for (i = 1; i <= RowN + PairA; i++){
	for (j = 1; j <= SCCount; j++) cout << SCM[i][j] << " "; 
	cout << endl;
}
stat = glp_mip_status(lp);		
cout << "GLP_OPT : " << GLP_OPT << ", Status = " << i <<"\n";								
						if (stat != GLP_FEAS && stat != GLP_OPT){
							cout << "exception found at p,pp,q,r = " << p << " " << pp << " " << q << " " << r << "\n";
							for (i = 1; i <= dega; i++) cout << sigma[i] << " ";
							cout << "\n";
							for (i = 1; i <= degb; i++) cout << tau[i] << " ";							
							cout << "\n";
							cout << "Error Code = " << stat << "\n";
							return 0;
						}
						glp_delete_prob(lp);
						next: {}					
					} while (next_permutation (tau + 1, tau + 1 + degb ));
				} while (next_permutation (sigma + 1 , sigma + 1 + dega));
			}	
	cout << "No exception to the Tiling Conjecture was found when the length = " << l << ".\n";
	return 1;
}	


int main ()
{

	int l;
	cout << "enter the length : ";
	cin >> l;
	checkpolygonality(l);

	return 0;
}
