#include "stdio.h"
#include "string.h"

void main ()
{
	void reverse (char * s, char * r)
	{
		int i, l;

		for (i = 0, l = strlen(s); i < l; i++)
			r[i] = s[l-i-1];
		r[i] = '\0';
	}

	char p [20];

	reverse("\n!dlrow olleH", p);
	writeString(p);
}
