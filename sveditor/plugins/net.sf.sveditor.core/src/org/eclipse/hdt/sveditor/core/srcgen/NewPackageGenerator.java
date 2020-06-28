/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.srcgen;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.indent.ISVIndenter;
import org.eclipse.hdt.sveditor.core.indent.SVIndentScanner;
import org.eclipse.hdt.sveditor.core.scanner.SVCharacter;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;
import org.eclipse.hdt.sveditor.core.tagproc.TagProcessor;

public class NewPackageGenerator {
	private TagProcessor		fTagProc;
	
	public NewPackageGenerator(TagProcessor proc) {
		fTagProc = proc;
	}
	
	public void generate(
			ISVDBIndexIterator	index_it,
			final IFile			file_path,
			String				pkg_name,
			IProgressMonitor	monitor) {
		
		fTagProc.setTag("filename", file_path.getName());
		fTagProc.setTag("type", "Package");
		SubMonitor subMonitor = SubMonitor.convert(monitor, "Creating package", 100);
		
		String template = "${file_header}\n";

		template += "/**\n";
		template += " * Package: " + pkg_name + "\n";
		template += " * \n";
		template += " * TODO: Add package documentation\n";
		template += " */\n";
		template += "package " + pkg_name;

		subMonitor.worked(25);
		
		template += ";\n";
		
		subMonitor.worked(25);
		
		template += "\n\n";
		template += "endpackage\n";
		
		template += "\n${file_footer}\n";
		
		template = fTagProc.process(template);

		subMonitor.subTask("Indenting content");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(new StringBuilder(template)));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		final StringInputStream in = new StringInputStream(indenter.indent());
		
		subMonitor.worked(25);
		
		try {
			if (file_path.exists()) {
				file_path.setContents(in, true, true, new NullProgressMonitor());
			} else {
				file_path.create(in, true, new NullProgressMonitor());
			}
		} catch (CoreException e) {}
		
		subMonitor.done();
	}
	
}
