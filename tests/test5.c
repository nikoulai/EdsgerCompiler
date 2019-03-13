#include "stdio.h"

void bsort (int * x, int n)
{
	int i;
	bool changed;

	void swap (byref int x, byref int y)
	{
		int t;

		t = x;
		x = y;
		y = t;
	}

	for (changed = true; changed;)
		for (i = 0, changed = false; i < n-1; i++)
			if (x[i] > x[i+1]) {
				swap(x[i], x[i+1]);
				changed = true;
			}
}

void main ()
{
	void printArray (char * msg, int * x, int n)
	{
		int i;

		writeString(msg);
		for (i = 0; i < n; i++) {
			if (i > 0)
				writeString(", ");
			writeInteger(x[i]);
		}
		writeString("\n");
	}

	int i, x[16], seed;

	for (i = 0, seed = 65; i < 16; i++)
		x[i] = seed = (seed * 137 + 221 + i) % 101;
	printArray("Initial array: ", x, 16);
	bsort(x, 16);
	printArray("Sorted array: ", x, 16);
}
