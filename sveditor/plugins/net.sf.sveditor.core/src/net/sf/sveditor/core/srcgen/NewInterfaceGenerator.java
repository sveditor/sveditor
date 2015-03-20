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


package net.sf.sveditor.core.srcgen;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tagproc.TagProcessor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class NewInterfaceGenerator {
	private TagProcessor		fTagProc;
	
	public NewInterfaceGenerator(TagProcessor proc) {
		fTagProc = proc;
	}
	
	public void generate(
			ISVDBIndexIterator	index_it,
			final IFile			file_path,
			String				ifc_name,
			IProgressMonitor	monitor) {
		fTagProc.setTag("filename", file_path.getName());
		fTagProc.setTag("type", "Interface");
		
		if (monitor == null) {
			monitor = new NullProgressMonitor();
		}
		monitor.beginTask("Creating interface", 100);
		
		String template = "${file_header}\n";

		template += "/**\n";
		template += " * Interface: " + ifc_name + "\n";
		template += " * \n";
		template += " * TODO: Add interface documentation\n";
		template += " */\n";
		template += "interface " + ifc_name;

		monitor.worked(25);
		
		template += ";\n";
		
		monitor.worked(25);
		
		template += "\n\n";
		template += "endinterface\n";
		
		template += "\n${file_footer}\n";
		
		template = fTagProc.process(template);

		monitor.subTask("Indenting content");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(new StringBuilder(template)));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		final StringInputStream in = new StringInputStream(indenter.indent());
		
		monitor.worked(25);
		
		try {
			if (file_path.exists()) {
				file_path.setContents(in, true, true, new NullProgressMonitor());
			} else {
				file_path.create(in, true, new NullProgressMonitor());
			}
		} catch (CoreException e) {}
		
		monitor.done();
	}
	
}
