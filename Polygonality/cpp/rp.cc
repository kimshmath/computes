//	Reduced-Polygonality Checker
//	Sang-hyun (Sam) Kim (c) 2010
// 		
//	Note. 
//	If the length considered is larger than 15, change length,length2,length4 properly
//
// 	This program checks the reduced-polygonality in F_2.
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
gcc -Kc++ -I$HOME/glpk/include -c polyg_pos.cc
gcc -Kc++ -L$HOME/glpk/lib -o polyg_pos.exe polyg_pos.o -lglpk -lm
OR, 
g++ -I$HOME/glpk/include -c rp.cc
g++ -L$HOME/glpk/lib -o rp.exe rp.o -lglpk -lm
OR, 
icc -Kc++ -I$HOME/glpk/include -c polyg_pos.cc
icc -Kc++ -L$HOME/glpk/lib -o polyg_pos.exe polyg_pos.o -lglpk -lm 
./a.out < input.txt > output.txt
where input.txt contains the length (number only)

job.sge file looks as follows:
#$ -N rp
#$ -cwd
#$ -V
#$ -o rp_consoleout
#$ -e rp.err
#$ -l h_rt=47:59:00
#$ -pe serial 1
#$ -q normal
#$ -S /bin/sh

./rp.exe < in11 > out11

where in11 contains the number 11 only. Then, submit the jobs by 

ssh shkim@stampede.tacc.utexas.edu
qsub job.sge

To find out (and kill, if necessary) PID of the job
ps aux | grep shkim

*/
#include <iostream>
#include <algorithm>
#include <math.h>
#include <glpk.h>

#define dMAX 20 + 1	// maximum degree + 1
#define  REAL  double
// the number of rows of each matrix is binomial(d, 2) + p + 2q + 2r <= (d d + 3 d) / 2 = 135, if d = 15.
// <= 230, if d = 20

// the number of columns of each matrix is pqr + 2qr + p^2
#define length4 430	+ 1// the number of simple cycles never exceeds 200 if length <= 15
// the number of simple cycles never exceeds 430 if length <= 20

#define MAXALL 7 * length4 + 1 
// each column contains at most 7 (including the last row, which is 1) non-zero entries
// + 1 as we count from ar[1]... disregarding ar[0].

using namespace std;

int permt1[dMAX];
int permt2[dMAX];
int permt3[dMAX];
int permt4[dMAX];
int tau[dMAX];
int ia[MAXALL], ja[MAXALL];
REAL ar[MAXALL];

inline int PairPosition (int i, int j){ return (max(i,j) - 1) * (max(i,j) - 2) / 2 + min(i,j); }

long int binomial(int n, int r)
{	if (r == 0) return 1;
	else return n * binomial(n - 1,r - 1) / r;
}

long int factorial(int n)
{
	if (n == 0) return 1;
	else return n * factorial(n - 1);
}

int kset(int n, int k, int rank, int subset[]) {
    int x = 1,  i, position;
    long int r = rank;
	position = 1;
    for(i = 1; i <= k; i++) {  
        while( binomial(n - x, k - i) <= r) {
            r = r - binomial(n - x++, k - i);
        }
		subset[position++] = x++;
	}
	return 0;
}

int main ()
{
	int p, q, r, RowN, d;
	long int permt1i, permt3i, pqrcp, qrcq, pfac, pos1, pos2, pos3;
	int i, j, k, current, count, count1, count2, SCCount, elemcount, iatmp1, iatmp2, ed;
	glp_prob *lp;
	glp_smcp parm;
	glp_init_smcp(&parm);
	parm.msg_lev = GLP_MSG_OFF;
//	glp_iocp parm;
//	glp_init_iocp(&parm);
//	parm.msg_lev = GLP_MSG_OFF;
//	parm.presolve = GLP_ON;
//	parm.fp_heur = GLP_ON;
//	glp_smcp parmsmcp;
//	glp_init_smcp(&parmsmcp);
//	parmsmcp.msg_lev = GLP_MSG_OFF;

	
	
	cout << "Input the degree <= 15 : ";
	cin >> d;
	
	RowN = d * (d - 1) / 2;
	

			
	for (q = 0; q <= d / 2; q++)
		for (r = q; r <= d/2; r++){
	      	p = d - q - r;
	
			if (q == 0 && r == 0) continue;
			cout << "(p,q,r) = (" << p << ", "<<q << ", " <<r<<")\n";
			pqrcp = binomial(p + q + r,p);
			qrcq = binomial(q + r, q);
			pfac = factorial(p);
			ed = 2 * d - p;
			
			for (permt1i = 0; permt1i < pqrcp; permt1i++){
				kset(p + q + r, p, permt1i, permt1);
				for (i = 1; i <= p; i++) tau[i] = permt1[i];
				do {
					for (i = 1; i <= p; i++) if (tau[i] == i) goto next;
					permt3i = 0;
					do {
						kset(q + r, q, permt3i, permt3);
						j = 0;
						current = 1;
						k = 1;
						count = 1;
						count1 = 1;
						count2 = 1;
						do {
							while (k <= p && permt1[k] == current) {
								k++; current++;
							}
							if (count1 <= q && permt3[count1] == count) tau[count1++ + p] = current++;
							else tau[count2++ + p + q] = current++;
						} while (++count <= q + r);


 						// build matrix for reduce polygonality check, using tau[]
						SCCount = 1;				// number of columns
						elemcount = 1;				// number of non-zero elements		

						// simple path at b+ (type 1)
						for (i = 1; i <= r; i++)
							for (j = 1; j <= q; j++){
								iatmp1 = PairPosition(p + j, p + q + i);
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;

								pos1 = j;
								pos2 = q + i;

								if (pos1 > 1) {
									ia[elemcount] = RowN + pos1 - 1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}

								if (pos1 + 1 < pos2) {
									ia[elemcount] = RowN + pos1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;

									ia[elemcount] = RowN + pos2 - 1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}

								if (pos2 < ed) {
									ia[elemcount] = RowN + pos2;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
								}

								SCCount++;
							}						

							
						// simple path at b- (type 2)
						for (i = 1; i <= q; i++)
							for (j = 1; j <= r; j++){
								iatmp2 = PairPosition(tau[i + p], tau[j + p + q]);
								ia[elemcount] = iatmp2;
								ja[elemcount] = SCCount;
								ar[elemcount++] = -1;

								pos1 = q + r + i;
								pos2 = 2 * q + r + j;

								if (pos1 > 1) {
									ia[elemcount] = RowN + pos1 - 1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}

								if (pos1 + 1 < pos2) {
									ia[elemcount] = RowN + pos1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;

									ia[elemcount] = RowN + pos2 - 1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}

								if (pos2 < ed) {
									ia[elemcount] = RowN + pos2;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;
								}

								SCCount++;
							}




						// simple path at b+ - b- (type 3)
						for (i = 1; i <= r; i++)
							for (j = 1; j <= p; j++)
								for (k = 1; k <= r; k++){
									iatmp1 = PairPosition(p + q + i, j);
									iatmp2 = PairPosition(tau[j], tau[k + p + q]);

									if (iatmp1 != iatmp2) {
										ia[elemcount] = iatmp1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
										ia[elemcount] = iatmp2;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

									pos1 = q + i;
									pos2 = 2 * q + r + k;
									pos3 = 2 * q + 2 * r + j;

									if (pos1 > 1) {
										ia[elemcount] = RowN + pos1 - 1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

									if (pos1 + 1 < pos2) {
										ia[elemcount] = RowN + pos1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;

										ia[elemcount] = RowN + pos2 - 1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

									if (pos2 + 1 < pos3) {
										ia[elemcount] = RowN + pos2;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;

										ia[elemcount] = RowN + pos3 - 1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

								if (pos3 < ed) {
										ia[elemcount] = RowN + pos3;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
									}					

									SCCount++;
							}														

						// simple path at b- - b+ (type 4)
						for (i = 1; i <= q; i++)
							for (j = 1; j <= p; j++)
								for (k = 1; k <= q; k++){
									iatmp1 = PairPosition(p + k, j);
									iatmp2 = PairPosition(tau[i + p], tau[j]);

									if (iatmp1 != iatmp2) {
										ia[elemcount] = iatmp1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
										ia[elemcount] = iatmp2;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}				

									pos1 = k;
									pos2 = q + r + i;
									pos3 = 2 * q + 2 * r + j;		

									if (pos1 > 1) {
										ia[elemcount] = RowN + pos1 - 1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

									if (pos1 + 1 < pos2) {
										ia[elemcount] = RowN + pos1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;

										ia[elemcount] = RowN + pos2 - 1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

									if (pos2 + 1 < pos3) {
										ia[elemcount] = RowN + pos2;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;

										ia[elemcount] = RowN + pos3 - 1;
										ja[elemcount] = SCCount;
										ar[elemcount++] = -1;
									}

								if (pos3 < ed) {
										ia[elemcount] = RowN + pos3;
										ja[elemcount] = SCCount;
										ar[elemcount++] = 1;
									}					

									SCCount++;
							}														


									

						// Add bigon rows joining b+- (type 5)
						for (i = 1; i < p; i++)
							for (j = i + 1; j <= p; j++){
								iatmp1 = PairPosition(i,j);
								iatmp2 = PairPosition(tau[i],tau[j]);
								if (iatmp1 == iatmp2) goto next;
								ia[elemcount] = iatmp1;
								ja[elemcount] = SCCount;
								ar[elemcount++] = 1;
								ia[elemcount] = iatmp2;
								ja[elemcount] = SCCount;
								ar[elemcount++] = -1;
								pos1 = 2 * q + 2 * r + i;		
								pos2 = 2 * q + 2 * r + j;		

								if (pos1 > 1) {
									ia[elemcount] = RowN + pos1 - 1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}

								if (pos1 + 1 < pos2) {
									ia[elemcount] = RowN + pos1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;

									ia[elemcount] = RowN + pos2 - 1;
									ja[elemcount] = SCCount;
									ar[elemcount++] = -1;
								}

								if (pos2 < ed) {
									ia[elemcount] = RowN + pos2;
									ja[elemcount] = SCCount;
									ar[elemcount++] = 1;						
								}

								SCCount++;
							}
						SCCount--;	
						for (j = 1; j <= SCCount; j++)	{
							ia[elemcount] = RowN + 2 * d - p;
							ja[elemcount] = j;
							ar[elemcount++] = 1;
							}
						elemcount--;						

						// solve LP using ia[], ja[] and ar[]
						lp = glp_create_prob();
						glp_set_obj_dir(lp, GLP_MIN);
						glp_add_rows(lp, RowN + 2 * d - p);						
						for (i = 1; i <= RowN + 2 * d - p - 1; i++) glp_set_row_bnds(lp, i, GLP_FX, 0.0, 0.0);
						glp_set_row_bnds(lp, RowN + 2 * d - p, GLP_LO, 1.0, 0.0);
						glp_add_cols(lp, SCCount);
						for (j = 1; j <= SCCount; j++) {
							glp_set_col_bnds(lp, j, GLP_LO, 0.0, 0.0);
							glp_set_obj_coef(lp, j, 0.0);
						}						
						glp_load_matrix(lp, elemcount, ia, ja, ar);
						glp_simplex(lp, &parm);
						pos1 = glp_get_status(lp);
						glp_delete_prob(lp);

						if (pos1 != GLP_UNBND && pos1 != GLP_FEAS && pos1 != GLP_OPT){
							cout << "error " << k << " has occurred at p,q,r = " << p << " " << q << " " << r << "\n";
							for (i = 1; i <= d; i++) cout << tau[i] << " ";							
							cout << "\n";
							return 0;
						}						
						
						next: {}
					} while (++permt3i < qrcq);
				} while (next_permutation(tau + 1, tau + p + 1));
				
			}
		}
	cout << "Successfully verifed for d = \n" << d;
	return 0;
}
