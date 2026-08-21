// next_permutation
#include <iostream>
#include <algorithm>
#include <vector>


#define dMAX 15 + 1	// maximum degree + 1
#define  REAL  double
// the number of rows of each matrix is binomial(d, 2) + p + 2q + 2r <= (d d + 3 d) / 2 = 135, if d = 15.
// <= 230, if d = 20

// the number of columns of each matrix is pqr + 2qr + p^2
#define length4 200	+ 1// the number of simple cycles never exceeds 200 if length <= 15
// the number of simple cycles never exceeds 430 if length <= 20

#define MAXALL 7 * length4 + 1 
// each column contains at most 7 (including the last row, which is 1) non-zero entries
// + 1 as we count from ar[1]... disregarding ar[0].

using namespace std;

int permt1[dMAX];
int permt2[dMAX];
int permt3[dMAX];
int permt4[dMAX];


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

int scmatrix(int p, int q, int r, int tau[], int ia[], int ja[], int ar[]){
	
	
	return 0;
}

int main () {
	int p, q, r, RowN, d;
	long int permt1i, permt2i, permt3i, pqrcp, qrcq, pfac, pos1, pos2, pos3;
	int i, j, k, current, count, count1, count2, SCCount, elemcount, iatmp1, iatmp2, ed;
	REAL ar[MAXALL];
	int tau[dMAX] = {0, 1,3,5,2,4};
	int ia[MAXALL], ja[MAXALL];
	int scm[40][40];
	
	// debugging code:
	p = 1; q = 2; r = 2;
	d = p + q + r;
	
	ed = 2 * d - p;
	RowN = d * (d - 1) / 2;
	
	// debugging code:
	for (i = 1; i <= RowN + ed; i++)
		for (j = 1; j <= 40; j++)	scm[i][j] = 0;

	SCCount = 1;
	elemcount = 1;

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
		
	// debugging code from here
	for (i = 1; i <= elemcount; i++) scm[ia[i]][ja[i]] = ar[i];
	for (i = 1; i <= RowN + 2 * d - p; i++){
		for (j = 1; j <= SCCount; j++){
			k = scm[i][j];
			if (k == -1) cout << " " << k;
			else cout << "  " << k;
		}
		cout << "\n";
	}

	
	next: {}

	return 0;
}