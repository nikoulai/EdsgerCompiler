#include "stdio.h"

void main ()
{
	int n, k, i, seed;
	double sum;

	writeString("Give n: ");
	n = readInteger();
	writeString("Give k: ");
	k = readInteger();

	for (i = 0, sum = 0.0, seed = 65; i < k; i++)
		sum += (double) (seed = (seed * 137 + 221 + i) % n);

	if (k > 0) {
		writeString("Mean: ");
		writeReal(sum / (double) k);
		writeString("\n");
	}
}
