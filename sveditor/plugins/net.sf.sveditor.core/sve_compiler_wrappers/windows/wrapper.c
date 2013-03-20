#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <windows.h>
#include <string.h>
#include <memory.h>

int main(int argc, char **argv) {
  int i;
  const char *outfile = getenv("SVE_COMPILER_ARGS_FILE");
  FILE *fp = fopen(outfile, "w");
  
  
  for (i=1; i<argc; i++) {
  	if (!strncmp(argv[i], "+incdir+", 8)) {
  		const char *incdir = &argv[i][8];
		char *fullpath = (char *)malloc(32768);
		char *last;
		GetFullPathName(incdir, 32768, fullpath, &last);
		fprintf(fp, "+incdir+%s\n", fullpath);
		free(fullpath);
  	} else {
  		if (GetFileAttributes(argv[i]) != 0xFFFFFFFF) {
  			// Convert to full path
  			char *fullpath = (char *)malloc(32768);
  			char *last;
  			GetFullPathName(argv[i], 32768, fullpath, &last);
  			fprintf(fp, "%s\n", fullpath);
  			free(fullpath);
  		} else {
		  	fprintf(fp, "%s\n", argv[i]);
		}
	}
  }
  
  fclose(fp);
  
  exit(0);
}


