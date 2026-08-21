#include <iostream>
#include <math.h>
#include <glpk.h>

using namespace std;

#define length 14 	// max length of the words

//max. number of constraints expected
#define length2 200 // the number of pairs (at a's and b's)

//max. number of variables expected
#define length4 200	// the number of simple cycles never exceeds 200 if length <= 15

#define  REAL  double
#define MAXALL 5 * length4 + 1

int increasingq (int * tau, int degb, int r)
{
	int i;
	if (r <= 1) return 1;
	for (i = 1; i < r; i++)
		if (tau[degb - r + i] > tau[degb - r + 1 + i]) return 0;
	return 1;
}

// return the position of the pair (i,j) in 12, 13, 23, 14, 24, ... order
inline int PairPosition (int i, int j){ return (max(i,j) - 1) * (max(i,j) - 2) / 2 + min(i,j); }

int checkpolygonality (int l)
{
	int p,pp,q,r,i,j, ii,jj, iatmp1, iatmp2, dega, degb, elemcount,PairA,PairB,RowN, SCN,SCCount,solnfound, solnfound1, solnfound2,excepfound = 0;
	REAL ar[MAXALL];
	int ia[MAXALL];
	int ja[MAXALL];
	glp_prob *lp;
	glp_smcp parm;
	glp_init_smcp(&parm);
	parm.msg_lev = GLP_MSG_OFF;

	
 	int sigma[length], tau[length];

/*
// debuggin code;
	int sigma[6] = {0, 3, 2, 5, 1, 4}, tau[5] = {0, 2, 1, 3, 4};
*/
	
	for (r = 1; r <= l/2.0; r++)
		for (q = r; q <= l/2.0 -r; q++)
			for ( pp = 0; pp < l / 2.0 - q - r; pp++){
				p = l - pp - 2 * q - 2 * r;
				if (q - r > pp) continue;			// if graph not minimal, continue to next
				PairA = (p + q + r) * (p + q + r - 1) / 2;
				PairB = (pp + q + r) * (pp + q + r - 1) / 2;
				RowN = PairA + PairB + 1;
				SCN = p * (p - 1) / 2 + pp * (pp - 1) / 2 + q * (q - 1) + r * (r - 1) 
					+ p * pp * q * q + p * pp * r * r + q * q * r * r +  2 * (p + pp) * q * r;
				dega = p+q+r; degb = pp+q+r;	 
				for (i = 1; i <= dega; i++) sigma[i] = i;	// initialize permutations
				do {
					for (i = 1; i <= degb; i++) tau[i] = i;
					do {						
						// if the last r numbers of tau are not increasing, check is redundant
						SCCount = 1;
						elemcount = 1;
						solnfound = 0;
						
						
						if (r > 1) {
							for ( i = 1; i < r; i++)
								if (tau[degb - r + i] > tau[degb - r + i + 1]) {solnfound = 1; break;}
						}
						
						// Add bigon rows joining a+-
						for (i = 1; i < p && !solnfound; i++)
							for (j = i + 1; j <= p && !solnfound; j++){
								iatmp1 = PairPosition(i,j);
								iatmp2 = PairPosition(sigma[i],sigma[j]);
								if (iatmp1==iatmp2) solnfound = 1;
								else{
									ia[elemcount] = iatmp1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									ia[elemcount] = iatmp2;
									ja[elemcount] = SCCount++;
									ar[elemcount++] = -1;
								}
							}
							
						// Add bigon rows joining b + -
						for (i = 1; i < pp && !solnfound; i++)
							for (j = i + 1; j <= pp && !solnfound; j++){
								iatmp1 = PairPosition(i,j);
								iatmp2 = PairPosition(tau[i],tau[j]);
								if (iatmp1==iatmp2) solnfound = 1;
								else{
									ia[elemcount] = iatmp1 + PairA;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
									ia[elemcount] = iatmp2 + PairA;
									ja[elemcount] = SCCount++;
									ar[elemcount++] = -1;	
								}
							}


						// Add bigon rows joining a + b + 
						for (i = p + q + 1; i < p + q + r && !solnfound; i++)
							for (j = i + 1; j <= p + q + r && !solnfound; j++){
								iatmp1 = PairPosition(i,j);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								iatmp1 = PairPosition(i + pp - p, j + pp - p);		
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = 1;
							}

						// Add bigon rows joining a - b - 
						for (i = p + q + 1; i < p + q + r && !solnfound; i++)
							for (j = i + 1; j <= p + q + r && !solnfound; j++){
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
						for (i = pp + 1; i < pp + q && !solnfound; i++)
							for (j = i + 1; j <= pp + q && !solnfound; j++){
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
						for (i = p + 1; i < p + q && !solnfound; i++)
							for (j = i + 1; j <= p + q && !solnfound; j++){
								iatmp1 = PairPosition(i,j);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								iatmp1 = PairPosition(tau[pp+p+q-i+1],tau[pp+p+q-j+1]);
								ia[elemcount] = iatmp1 + PairA;
								ja[elemcount] = SCCount++;
								ar[elemcount++] = -1;
							}

						// Add square rows joining a + a - b - b + 
						for (i = 1; i <= p && !solnfound; i++)
							for(j = p + q + 1; j <= p + q + r && !solnfound; j++)
								for(ii = 1; ii <= pp && !solnfound; ii++)
									for(jj = p + q + 1; jj <= p + q + r && !solnfound; jj++){
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
										if (solnfound1 * solnfound2) solnfound = 1;
										else SCCount++;
									}
			
						// Add square rows joining a + b - a - b + 

						for(i = p + 1; i <= p + q && !solnfound; i++)
							for(j = p + q + 1; j <= p + q + r && !solnfound; j++)
								for(ii = pp + 1; ii <= pp + q && !solnfound; ii++)
									for(jj = p + q + 1; jj <= p + q + r && !solnfound; jj++){
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
										if (solnfound1 * solnfound2) solnfound = 1;
										else SCCount++;									
									}

						
						// Add square rows joining a + b - b + a - 			
						for(i = 1; i <= p && !solnfound; i++)
							for(j = p + 1; j <= p + q && !solnfound; j++)
								for(ii = 1; ii <= pp && !solnfound; ii++)
									for(jj = pp + 1; jj <= pp + q && !solnfound; jj++){
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
										if (solnfound1 * solnfound2) solnfound = 1;
										else SCCount++;																			
									}
						
						if (solnfound) continue;
						
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
						if (solnfound) continue;
						
						SCCount--;			// revert the last increment of Simple Cycle Counts
	
						// Add the last row consisting of 1's

						for (i = 1; i <= SCCount; i++){
							ia[elemcount] = RowN;
							ja[elemcount] = i;
							ar[elemcount++] = 1;
						}

						elemcount--;		// revert the last increment of non-zero entry counts

						lp = glp_create_prob();
						glp_set_obj_dir(lp, GLP_MIN);
						glp_add_rows(lp, RowN);
						for (i = 1; i < RowN; i++) glp_set_row_bnds(lp, i, GLP_FX, 0.0, 0.0);
						glp_set_row_bnds(lp, RowN, GLP_LO, 1.0, 0.0);
						glp_add_cols(lp, SCCount);
						for (j = 1; j <= SCCount; j++) {
							glp_set_col_bnds(lp, j, GLP_LO, 0.0, 0.0);
							glp_set_obj_coef(lp, j, 0.0);
						}
						glp_load_matrix(lp, elemcount, ia, ja, ar);
						glp_simplex(lp, &parm);
						if (glp_get_status(lp) == 5) solnfound = 1;
						if (!solnfound) {
							cout << "exception found at p,pp,q,r = " << p << " " << pp << " " << q << " " << r << "\n";
							for (i = 1; i <= dega; i++) cout << sigma[i] << " ";
							cout << "\n";
							for (i = 1; i <= degb; i++) cout << tau[i] << " ";							
							cout << "\n";
							excepfound = 1;
						}

						glp_delete_prob(lp);	
	

	
//debugging code
//cout << "p,pp,q,r" << p << pp << q << r			<< ", elemcount, SCCount = " << elemcount << ", " << SCCount << "\n";
/*
for (i = 1; i <= elemcount - 1; i++) SCM[ia[i]][ja[i]] = ar[i];
for (i = 1; i <= RowN; i++){
	for (j = 1; j <= SCCount - 1; j++){
		if (SCM[i][j] == -1) cout << SCM[i][j] <<" ";
		else cout << " " << SCM[i][j] << " ";
		}
		cout << "\n";
}
*/
// for (i = 1; i <= elemcount - 1; i++) cout	<< "ia = " << ia[i] << ", ja = " << ja[i] << ", ar = " << ar[i] << "\n";





// debugging code 
// cout << "permutation changes\n";	
						
					} while (next_permutation (tau + 1, tau + 1 + degb ) && !excepfound);
				} while (next_permutation (sigma + 1 , sigma + 1 + dega) && !excepfound);
			}	
			
	cout << "\n excepfound = " << excepfound;
	return 1;
}	


int main ()
{

	int l = 12;
	
	checkpolygonality(l);

	return 0;
}
