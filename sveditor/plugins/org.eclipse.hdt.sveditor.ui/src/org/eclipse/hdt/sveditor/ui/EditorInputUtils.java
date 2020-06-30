/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;

public class EditorInputUtils {
	
	public static Tuple<File, IFile> getFileLocation(IEditorInput input) {
		File file = null;
		IFile ifile = null;
		
		if (input instanceof IFileEditorInput) {
			ifile = ((IFileEditorInput)input).getFile();
		} else if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			file = new File(uri.getPath());
		}
		
		return new Tuple<File, IFile>(file, ifile);
	}
	
	public static InputStream openInputStream(IEditorInput input) {
		InputStream in = null;
		
		if (input instanceof IFileEditorInput) {
			IFile file = ((IFileEditorInput)input).getFile();
			for (int i=0; i<2; i++) {
				try {
					in = file.getContents();
					break;
				} catch (CoreException e) {
					if (e.getMessage().contains("out of sync")) {
						try {
							file.getParent().refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());
						} catch (CoreException e2) {

						}
					}
				}
			}
		} else if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			try {
				in = new FileInputStream(uri.getPath());
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		return in;
	}

	public static void setContents(IEditorInput input, InputStream in) throws Exception {
		if (input instanceof IFileEditorInput) {
			IFile file = ((IFileEditorInput)input).getFile();
			file.setContents(in, true, true, new NullProgressMonitor());
		} else if (input instanceof IURIEditorInput) {
			OutputStream out = null;
			URI uri = ((IURIEditorInput)input).getURI();
			byte tmp[] = new byte[4096];
			int len;
			
			out = new FileOutputStream(uri.getPath());
			
			while ((len = in.read(tmp, 0, tmp.length)) > 0) {
				out.write(tmp, 0, len);
			}
			out.close();
		}
	}
}
