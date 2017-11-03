#include<stdio.h>

int main() {
	int a = 5;
	int b = 10;
	int c = a + b;

	if(a > 5) {
		a = a + b;
		c = b - a;
	}

	else {
		int d = a + b;
		int e = a - c;
	}

	b = c - a;


	return 0;
}
