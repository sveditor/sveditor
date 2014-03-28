/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <windows.h>
#include <string.h>
#include <memory.h>

static const char *ARGS_FILENAME_ENV = "SVE_COMPILER_ARGS_FILE";

int main(int argc, char **argv) {
  int i;
  const char *outfile = getenv(ARGS_FILENAME_ENV);
  FILE *fp = fopen(outfile, "a");
  char *tmp = (char *)malloc(32768);
  
  GetCurrentDirectory(32768, tmp);
  fprintf(fp, "-SVE_SET_CWD %s\n", tmp);
  free(tmp);
  
  
  for (i=1; i<argc; i++) {
  	if (!strncmp(argv[i], "+incdir+", 8)) {
  	/*
  		const char *incdir = &argv[i][8];
		char *fullpath = (char *)malloc(32768);
		char *last;
		GetFullPathName(incdir, 32768, fullpath, &last);
		fprintf(fp, "+incdir+%s\n", fullpath);
		free(fullpath);
	 */
	 fprintf(fp, "%s\n", argv[i]);
  	} else {
  	/*
  		if (GetFileAttributes(argv[i]) != 0xFFFFFFFF) {
  			// Convert to full path
  			char *fullpath = (char *)malloc(32768);
  			char *last;
  			GetFullPathName(argv[i], 32768, fullpath, &last);
  			fprintf(fp, "%s\n", fullpath);
  			free(fullpath);
  		} else {
  	 */
		  	fprintf(fp, "%s\n", argv[i]);
	/*		  	
		}
	 */
	}
  }
  
  fclose(fp);
  
  exit(0);
}


