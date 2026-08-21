// next_permutation
#include <iostream>
#include <algorithm>
#include <vector>

#define dMAX 20
#define  REAL  double
#define length4 200	// the number of simple cycles never exceeds 200 if length <= dMAX

#define MAXALL 5 * length4 + 1 
// each column contains at most 5 (including the last row, which is 1) non-zero entries
// + 1 as we count from ar[1]... disregarding ar[0].

using namespace std;

int permt1[dMAX];
int permt2[dMAX];
int permt3[dMAX];
int permt4[dMAX];
int tau[dMAX] = {0, 5, 3, 1, 2, 4, 6};
int ia[MAXALL], ja[MAXALL];

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
	int p, q, r, RowN, d = 5;
	long int permt1i, permt2i, permt3i, pqrcp, qrcq, pfac, pos1, pos2, pos3;
	int i, j, k, current, count, count1, count2, SCCount, elemcount, iatmp1, iatmp2, ed;
	REAL ar[MAXALL];
	int ia[MAXALL], ja[MAXALL];

	ed = 2 * d - p;
	RowN = d * (d - 1) / 2;
	
	for (q = 0; q <= d / 2; q++)
		for (r = q; r <= d/2; r++){
	      	p = d - q - r;
			if (q == 0 && r == 0) continue;
			cout << "(p,q,r) = (" << p << ", "<<q << ", " <<r<<")\n";
			pqrcp = binomial(p + q + r,p);
			qrcq = binomial(q + r, q);
			pfac = factorial(p);
			
			for (permt1i = 0; permt1i < pqrcp; permt1i++){
				kset(p + q + r, p, permt1i, permt1);
				for (i = 1; i <= p; i++) tau[i] = permt1[i];
				do {
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
						//debugging code
						for (i = 1; i <= d; i++) cout << tau[i];
						cout << "\n";
						
						
						
						
					} while (++permt3i < qrcq);
				} while (next_permutation(tau + 1, tau + p + 1));
				
			}
		}
	return 0;
}
