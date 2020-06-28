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
package net.sf.sveditor.ui.console;

import java.io.File;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.ui.console.FileLink;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.ui.console.IPatternMatchListener;
import org.eclipse.ui.console.TextConsole;

import net.sf.sveditor.ui.script.launch.ExternalPathHyperlink;

public abstract class SVPatternMatcherBase implements IPatternMatchListener {
	protected TextConsole			fConsole;

	@Override
	public void connect(TextConsole console) {
		fConsole = console;
	}

	@Override
	public void disconnect() {
		// TODO Auto-generated method stub

	}
	
	protected void addIFileLink(
			IFile file, 
			int lineno,
			int offset,
			int length) {
		FileLink link = new FileLink(file, null, -1, -1, lineno);
		try {
			fConsole.addHyperlink(link, offset, length);
		} catch (BadLocationException e) {}
	}
	
	protected void addFSFileLink(
			File	file,
			int		lineno,
			int		offset,
			int		length) {
		IFileStore fs = EFS.getLocalFileSystem().getStore(new Path(file.getAbsolutePath()));
		ExternalPathHyperlink link = new ExternalPathHyperlink(fs, null, -1, -1, lineno);
		try {
			fConsole.addHyperlink(link, offset, length);
		} catch (BadLocationException e) {}
	}

	@Override
	public int getCompilerFlags() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String getLineQualifier() {
		// TODO Auto-generated method stub
		return null;
	}
}
