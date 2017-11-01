#include<stdio.h>

int main() {
	int a = 5;
	int b = 10;
	int c = a + b;

	if(a > 5) {
		a = a + b;
		c = a + b;
	}

	else {
		int d = a + b;
	}

	return 0;
}
