// List of injective maps from {1,...,p} to {1,...,p+r}.\n"
#include <iostream>
#define dMAX 20
using namespace std;
int f[dMAX];

long int binomial(int n, int r)
{	if (r == 0) return 1;
	else return n*binomial(n-1,r-1)/r;
}

int SubsetFromRank(int n, int k, int rank, int subset[]) {
    int x = 1,  i, position = 0;
    long int r = rank;
    for(i=1; i <= k; i++) {
        while( binomial(n-x, k-i) <= r) r -= binomial(n - x++, k - i);
		subset[position++] = x++;
	}
	return 0;
}

int main () {
	int p, r, rank, i;
	p = 3; r = 4;
	for (rank = 0; rank < binomial(p + r, p); rank++){
		SubsetFromRank(p + r, p, rank ,f);
		do{ 
			for (i = 0; i < p; i++) cout << f[i];
			cout << "\n";
		} while (next_permutation(f, f + p));
	}
	return 0;
}