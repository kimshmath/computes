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
int tau[dMAX] = {0, 5, 3, 1, 2, 7, 4, 6};
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

int main () {
	int i, j;

	for (i = 0; i < 20; i++){
		kset(6, 3, i, permt1);
		for (j = 1; j <= 3; j++) cout << permt1[j] << " ";
		cout << "\n";
	}
	return 0;
}



















