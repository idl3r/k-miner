#include <stdio.h>
#include <stdlib.h>

struct request {
	char *cmd;
};

// should be replaced
void* vmalloc() {
	printf("do something\n");
	return malloc(42);
}

// should be replaced
void kfree(void *cmd) {
	printf("do something %p\n", cmd);
}

void sys_test() {
	char *c = (char*)vmalloc();
	struct request rq;

	rq.cmd = c;

	if(c)
		kfree(c);

	if(rq.cmd)
		kfree(rq.cmd);
}

int main() {
	sys_test();
	return 0;
}
