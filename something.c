#include<stdio.h>

int main() {
	int a = 5;
	int b = 10;
	int c = a + b;
	if(a>b) {
		a = a + b;
		c = a + b;
	}
	else {
	 	a = a + b;
	}
	return 0;
}
