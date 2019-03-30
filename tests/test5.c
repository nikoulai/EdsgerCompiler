#include "stdio.h"
void rrr(char * msg, int * x, int n);

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

	for (i = 0, seed = 65; i < 16; i++){
		writeInteger((seed * 137 + 221 + i) % 101);
		x[i] = seed = (seed * 137 + 221 + i) % 101;
		// seed =x[i] = (seed * 137 + 221 + i) % 101;
		 // x[i]= (seed * 137 + 221 + i) % 101;



	writeString("!!\n");
	writeString("x[i]: ");
	writeInteger(x[i]);
	writeString(" seed:");
	writeInteger(seed);
	writeString(" ");
	writeInteger(x[i]-seed);
	writeChar('\n');
}

	printArray("Initial array: ", x, 16);
	bsort(x, 16);
	printArray("Sorted array: ", x, 16);
}
