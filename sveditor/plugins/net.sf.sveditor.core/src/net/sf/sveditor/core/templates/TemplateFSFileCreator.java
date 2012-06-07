/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.templates;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class TemplateFSFileCreator implements ITemplateFileCreator {
	
	private File						fRoot;
	
	public TemplateFSFileCreator(File root) {
		fRoot = root;
	}

	
	public void createFile(String path, InputStream content) {
		File file = new File(fRoot, path);
		byte tmp[] = new byte[16384];
		int len;
		
		if (!file.getParentFile().exists()) {
			file.getParentFile().mkdirs();
		}
		
		try {
			FileOutputStream fos = new FileOutputStream(file);
			
			while ((len = content.read(tmp, 0, tmp.length)) > 0) {
				fos.write(tmp, 0, len);
			}

			fos.close();
		} catch (IOException e) { }
	}


	public OutputStream openStream(String path) {
		File target = new File(fRoot, path);
		try {
			return new FileOutputStream(target);
		} catch (IOException e) {}

		return null;
	}

	public void closeStream(OutputStream out) {
		try {
			out.close();
		} catch (IOException e) {}
	}

}
