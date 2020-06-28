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
package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

public class SVDBScopedFileSystemProvider extends SVDBFSFileSystemProvider {
	private String					fRoot;
	private String					fRootName;
//	private String					fRootParent;
	
	public void init(String root) { 
		init(root, new File(root).getName());
	}

	public void init(String root, String name) {
		fRoot = root.replace('\\', '/');
		fRootName = name;
	}

	@Override
	public List<String> getFiles(String path) {
		List<String> ret = null;
		
		if (path.equals("/")) {
			ret = new ArrayList<String>();
			ret.add("/" + fRootName);
		} else {
			String effective_path = getEffectivePath(path);

			ret = super.getFiles(effective_path);

			// Trim path
			String prefix = fRoot;
			for (int i=0; i<ret.size(); i++) {
				String p = ret.get(i);
				String p2 = "/" + fRootName + p.substring(prefix.length());
				ret.set(i, p2);
			}
		}
		
		return ret;
	}
	
	private String getEffectivePath(String path) {
		String ret = fRoot + path.substring(fRootName.length()+1);
		return ret;
	}
	

	@Override
	public boolean fileExists(String path) {
		String effective_path = getEffectivePath(path);
		return super.fileExists(effective_path);
	}

	@Override
	public boolean isDir(String path) {
		String effective_path = getEffectivePath(path);
		return super.isDir(effective_path);
	}

	public InputStream openStream(String path) {
		String effective_path = getEffectivePath(path);
		return super.openStream(effective_path);
	}

	@Override
	public OutputStream openStreamWrite(String path) {
		String effective_path = getEffectivePath(path);
		return super.openStreamWrite(effective_path);
	}

	@Override
	public long getLastModifiedTime(String path) {
		String effective_path = getEffectivePath(path);
		return super.getLastModifiedTime(effective_path);
	}

}
