#include <iostream>
#include <math.h>
#include <set>
#include <new>
#include <vector>
#include <glpk.h>

using namespace std;

#define length 14
#define length2 200             
#define length4 200	// the number of simple cycles never exceeds 200 if length <= 15
#define NMAX  length4  //max. number of variables expected
#define MMAX  length2  //max. number of constraints expected
#define MAXALL length2*length4
#define  REAL  double      

typedef REAL MAT[MMAX+3][NMAX+2];
int  IPOSV[MMAX], IZROV[NMAX];

glp_prob *lp;
	
MAT SCM;
int SCN;
int ICASE;
REAL ar[MAXALL];
int ia[MAXALL];
int ja[MAXALL];


// the position (pair index) of the (i,j) in 12,13,23,14,24,34... order
// return 0 for empty pair
int PairPosition (int i, int j){
	return (j - 1) * (j - 2) / 2 + i;}

// when the deg(a)=dA, find the k-th pair in 12,13,.. order, 
// and write the result on *pair
int PositionToPair (int da, int k, int * pair)
{
	int ACorner = da * (da - 1)/2, i, j;
	
	if (k > ACorner) k -= ACorner;
	j = int( ceil((1 + sqrt(1 + 8 * float(k))) / 2 ));
	i = k - (j - 1) * (j - 2) / 2;
	*pair = i;
	*(pair+1) = j;
	return 0;
}

// make a vector (0,0,1,0,-1,0,...) using pairlist of the form {2,5,7,6}
// in this example, 2 is the pair index at a+, 5 is at a-, etc
// put 1 in the position 2-1, put -1 in the position 5-1, put 1 in the position 7-1+PairA(=deg a(deg a-1)/2), put -1 in the ...
// and then, write the result on pairvec
int PairVector (int PairA, int PairB, int * pairlist, int * pairvec)
{
	int i;
	for (i = 0; i < PairA + PairB; i++) *(pairvec + i) = 0;
	for (i = 0; i < 4; i++){
		if (*(pairlist + i) == 0) continue;
		*(pairvec + *(pairlist + i) - 1	 + PairA * int(floor(float(i)/2) )) +=  1 + 4 * floor(float(i)/2)- 2 * i;
	}
	return 0;
}
	
int SCMatrix (int p, int pp, int q, int r, int * sigma, int * tau, int PairA, int PairB)
{
	int RowN, i, j, k, ii,jj, SCCount = 0, SCListTmp[4], SCMTmp[length2];
	RowN = PairA + PairB; // number of rows of SCMatrix
	
	// Add bigon rows joining a+-
	for (i = 1; i < p; i++){
		for (j = i + 1; j <= p; j++){
			SCListTmp[0] = PairPosition(i,j);	// SCListTmp is the simple cycle list of the form {x,y,z,w}
			SCListTmp[1] = PairPosition(sigma[i-1],sigma[j-1]); // where x,y,.. are the indices of the pairs at a+,a-,...
			SCListTmp[2] = 0;									// note that sigma(i) is stored as sigma[i-1]
			SCListTmp[3] = 0;
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				// compute SCCount-th column of SCM, writing on SCMTmp
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	// SCList[][SCCount] is the SCCount-th simple cycle list
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		// SCM[][SCCount] is the SCCount-th column of SCM
			SCCount++;	
		}
	}

	// Add bigon rows joining b + -
	for (i = 1; i < pp; i++){
		for (j = i + 1; j <= pp; j++){
			SCListTmp[0] = 0;	// SCListTmp is the simple cycle list of the form {x,y,z,w}
			SCListTmp[1] = 0; // where x,y,.. are the indices of the pairs at a+,a-,...
			SCListTmp[2] = PairPosition(i,j);
			SCListTmp[3] = PairPosition(tau[i-1],tau[j-1]); 			// note that tau(i) is stored as tau[i-1]
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				// compute SCCount-th column of SCM, writing on SCMTmp
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	// SCList[][SCCount] is the SCCount-th simple cycle list
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		// SCM[][SCCount] is the SCCount-th column of SCM
			SCCount++;	
		}
	}
	// Add bigon rows joining a + b + 
	for (i = p+q+1; i < p+q+r; i++){
		for (j = i+1; j <= p+q+r; j++){
			SCListTmp[0] = PairPosition(i,j);	
			SCListTmp[1] = 0; 
			SCListTmp[2] = PairPosition(i+pp-p,j+pp-p);
			SCListTmp[3] = 0;
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
	}
	
	// Add bigon rows joining a - b - 
	for (i=p+q+1; i<p+q+r; i++){
		for (j=i+1; j<=p+q+r; j++){
			SCListTmp[0] = 0;	
			SCListTmp[1] = PairPosition(sigma[i-1],sigma[j-1]); 
			SCListTmp[2] = 0;
			SCListTmp[3] = PairPosition(tau[i+pp-p-1],tau[j+pp-p-1]);
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
	}
	
	 // Add bigon rows joining a - b + 
	for (i=pp+1; i<pp+q; i++){
		for (j=i+1; j<=pp+q; j++){
			SCListTmp[0] = 0;	
			SCListTmp[1] = PairPosition(sigma[pp+p+q-i],sigma[pp+p+q-j]); 
			SCListTmp[2] = PairPosition(i,j);
			SCListTmp[3] = 0;
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
	}


	// Add bigon rows joining a + b -
	for (i = p + 1; i < p + q; i++){
		for(j = i + 1; j <= p + q; j++){
			SCListTmp[0] = PairPosition(i,j);	
			SCListTmp[1] = 0;
			SCListTmp[2] = 0;
			SCListTmp[3] = PairPosition(tau[pp+p+q-i],tau[pp+p+q-j]);
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
	}


	// Add square rows joining a + a - b - b + 
	for (i = 1; i <= p; i++)
		for(j = p + q + 1; j <= p + q + r; j++)
			for(ii = 1; ii <= pp; ii++)
				for(jj = p + q + 1; jj <= p + q + r; jj++){
					SCListTmp[0] = PairPosition(i,j);	
					SCListTmp[1] = PairPosition(sigma[i-1],sigma[jj-1]); 
					SCListTmp[2] = PairPosition(ii,j+pp-p);
					SCListTmp[3] = PairPosition(tau[ii-1],tau[jj+pp-p-1]);
					PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//					for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
					for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
					SCCount++;	
				}

	// Add square rows joining a + b - a - b + 

	for(i = p + 1; i <= p + q; i++)
		for(j = p + q + 1; j <= p + q + r; j++)
			for(ii = pp + 1; ii <= pp + q; ii++)
				for(jj = p + q + 1; jj <= p + q + r; jj++){
					SCListTmp[0] = PairPosition(i,j);	
					SCListTmp[1] = PairPosition(sigma[jj-1],sigma[pp+p+q-ii]); 
					SCListTmp[2] = PairPosition(ii,j+pp-p);
					SCListTmp[3] = PairPosition(tau[pp+p+q-i],tau[jj+pp-p-1]);
					PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//					for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
					for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
					SCCount++;	
				}

	// Add square rows joining a + b - b + a - 			
	
	for(i = 1; i <= p; i++)
		for(j = p + 1; j <= p + q; j++)
			for(ii = 1; ii <= pp; ii++)
				for(jj = pp + 1; jj <= pp + q; jj++){
					SCListTmp[0] = PairPosition(i,j);	
					SCListTmp[1] = PairPosition(sigma[i-1],sigma[pp+p+q-jj]); 
					SCListTmp[2] = PairPosition(ii,jj);
					SCListTmp[3] = PairPosition(tau[pp+p+q-j],tau[ii-1]);
					PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//					for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
					for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
					SCCount++;	
				}

	// Add triangles joining a + b + a - 
	for(i = 1; i <= p; i++)
	  for(j = p + q + 1; j <= p + q + r; j++)
	    for(ii = pp + 1; ii <= pp + q; ii++){
			SCListTmp[0] = PairPosition(i,j);	
			SCListTmp[1] = PairPosition(sigma[i-1],sigma[pp+p+q-ii]); 
			SCListTmp[2] = PairPosition(ii,j+pp-p);
			SCListTmp[3] = 0;
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
					


	// Add triangles joining a+b+b- 
	for(i = p + 1; i <= p + q; i++)
	  for(j = p + q + 1; j <= p + q + r; j++)
	    for(ii = 1; ii <= pp; ii++){
			SCListTmp[0] = PairPosition(i,j);	
			SCListTmp[1] = 0;
			SCListTmp[2] = PairPosition(ii,j+pp-p);
			SCListTmp[3] = PairPosition(tau[ii-1],tau[pp+p+q-i]);
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}		


	// Add triangles joining a+a-b- 
	for(i = 1; i <= p; i++)
	  for(j = p + 1; j <= p + q; j++)
	    for(ii = p + q + 1; ii <= p + q + r; ii++){
			SCListTmp[0] = PairPosition(i,j);	
			SCListTmp[1] = PairPosition(sigma[i-1],sigma[ii-1]); 
			SCListTmp[2] = 0;
			SCListTmp[3] = PairPosition(tau[ii+pp-p-1],tau[pp+p+q-j]);
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
	
	// Add triangles joining a-b+b- 
	for(i = 1; i <= pp; i++)
	  for(j = pp + 1; j <= pp + q; j++)
	    for(ii = p + q + 1; ii <= p + q + r; ii++){
			SCListTmp[0] = 0;
			SCListTmp[1] = PairPosition(sigma[ii-1],sigma[pp+p+q-j]); 
			SCListTmp[2] = PairPosition(i,j);	
			SCListTmp[3] = PairPosition(tau[i-1],tau[ii+pp-p-1]);
			PairVector(PairA, PairB, SCListTmp, SCMTmp);				
//			for (k = 0; k < 4; k++) SCList[k][SCCount] = SCListTmp[k];	
			for (k = 0; k < RowN; k++) SCM[k+2][SCCount+1] = SCMTmp[k];		
			SCCount++;	
		}
	
	// Add non-triviality condition (i.e. a row consisting of 1's)
	
		
/* begin : for debugging 
	for (i = 0; i < SCCount; i++){
		for (j = 0; j < 4; j++){
			cout << SCList[j][i] << " ";
		}
		cout << endl;
	}
	// print the matrix computed so far
	for (i = 0; i < RowN; i++){
		for (j = 0; j < SCCount; j++) cout << SCM[i][j] << " "; 
	cout << endl;
	}
	cout << SCCount;

end : for debugging */

	return 0;
}
		
int increasingq (int * tau, int degb, int r)
{
	int i;
	if (r <= 1) return 1;
	for (i = 1; i <= r; i++)
		if (tau[degb - r - 1 + i] > tau[degb - r + i]) return 0;
	return 1;
}

int checkpolygonality (int l)
{
	int p,pp,q,r,i, j, dega, degb, PairA, PairB;
	int sigma[length], tau[length];
	glp_smcp parm;
	glp_init_smcp(&parm);
	parm.msg_lev = GLP_MSG_OFF;

	
	for (r = 1; r <= l/2; r++)
		for (q = r; q <= l/2 -r; q++)
			for ( pp = 0; pp < l/2 - q - r; pp++){
				p = l - pp - 2 * q - 2 * r;
				if (q-r > pp) continue;
				dega = p+q+r; degb = pp+q+r;
				SCN = p * (p - 1) / 2 + pp * (pp - 1) / 2 + q * (q - 1) + r * (r - 1) + p * pp * q * q + p * pp * r * r + q * q * r * r +  2 * (p + pp) * q * r;
				PairA =dega * (dega - 1) / 2;
				PairB = degb * (degb - 1) / 2;
				for (i = 0; i < dega; i++) sigma[i] = i+1;
				do {
					for (i = 0; i < degb; i++) tau[i] = i+1;
					do {
if (increasingq (tau, degb, r) == 0) continue;
SCMatrix(p,pp,q,r,sigma,tau,PairA,PairB); 

lp = glp_create_prob();
glp_set_prob_name(lp, "SCMatrix");
glp_set_obj_dir(lp, GLP_MIN);
glp_add_rows(lp, PairA+PairB+1);
SCMatrix(p,pp,q,r,sigma,tau,PairA,PairB); 
glp_set_row_bnds(lp, 1, GLP_LO, 1.0, 0.0);
for (i = 2; i <= PairA + PairB + 1; i++) glp_set_row_bnds(lp, i, GLP_FX, 0.0, 0.0);
glp_add_cols(lp, SCN);
for (j = 1; j <= SCN; j++) {
	glp_set_col_bnds(lp, j, GLP_LO, 0.0, 0.0);
	glp_set_obj_coef(lp, j, 0.0);
}

for (i = 1; i <= PairA + PairB + 1; i++)
	for (j = 1; j <= SCN; j++){
		ia[SCN*(i-1)+ j] = i;
		ja[SCN*(i-1)+ j] = j;		
		ar[SCN*(i-1)+ j] = SCM[i][j];
		}

glp_load_matrix(lp, SCN * (PairA+PairB+1), ia, ja, ar);
glp_simplex(lp, &parm);
cout << "result = " << glp_get_status(lp) << "\n";
glp_delete_prob(lp);		
/*
simplx(SCM,PairA+PairB+1,SCN,0,1,PairA+PairB,&ICASE,IZROV,IPOSV);
if (ICASE == 0 ) continue;
else {
	cout << "ICASE = " << ICASE << "\n";
	cout << "A counter-example found at (p,pp,q,r) = (" << p << ", " << pp << ", " << q << ", " << r << ")\n";
	cout << "(sigma, tau) = (";
	for (i = 0; i < dega; i++) cout << sigma[i] << " ";
 	cout << ", ";
 	for (i = 0; i < degb; i++) cout << tau[i] << " ";
 	cout << ")\n";
	return 0; 
}
*/
					} while (next_permutation (tau, tau + degb));
				} while (next_permutation (sigma, sigma + dega));
			}
	cout << "looks good";
	return 1;
	
}	


int main ()
{

	int p,pp,q,r, PairA, PairB, l = length,dega, degb, i, j;
	int sigma[length]= {7,5,2,6,3,1,8,4}, tau[length] = {2,3,6,1,4,5};

	for (i = 1 ; i <= MMAX + 2; i++)			for (j = 1; j <= NMAX + 1; j++) SCM[i][j] = 0;
	for (j = 1; j <= NMAX; j++) SCM[1][j] = 1;
	
	l = 6;
	checkpolygonality (l);
/*
	l = 14;
	p = 2; pp = 1; q = 3; r = 0;

	SCN = p * (p - 1) / 2 + pp * (pp - 1) / 2 + q * (q - 1) + r * (r - 1) + p * pp * q * q + p * pp * r * r + q * q * r * r +  2 * (p + pp) * q * r;
	PairA = (p + q + r) * (p + q + r - 1) / 2;
	PairB = (pp + q + r) * (pp + q + r - 1) / 2;
	SCMatrix(p,pp,q,r,sigma,tau,PairA,PairB);

// for debugging
	for (i = 1; i <= PairA+PairB; i++){
			for (j = 1; j <= SCN+1; j++) cout << SCM[i][j] << " "; 
		cout << endl;
		}

*/
	
	
	
	return 0;
}
