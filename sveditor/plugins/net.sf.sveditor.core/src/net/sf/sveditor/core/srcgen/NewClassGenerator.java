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

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.tagproc.TagProcessor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;

public class NewClassGenerator {
	
	private TagProcessor			fTagProc;
	
	public NewClassGenerator(TagProcessor proc) {
		fTagProc = proc;
	}
	
	public void generate(
			ISVDBIndexIterator	index_it,
			final IFile			file_path,
			String				clsname,
			String				superclass,
			boolean				implement_new,
			IProgressMonitor	monitor) {
		fTagProc.setTag("filename", file_path.getName());
		fTagProc.setTag("type", "Class");
		
		SubMonitor sm = SubMonitor.convert(monitor, "Creating class", 100);
		
//		subst_filename = SVCharacter.toSVIdentifier(file_path.getName());
		
		String template = "${file_header}\n";

		template += "/**\n";
		template += " * Class: " + clsname + "\n";
		template += " * \n";
		template += " * TODO: Add class documentation\n";
		template += " */\n";
		template += "class " + clsname;

		SVDBClassDecl superclass_decl = null;
		if (superclass != null && 
				!superclass.trim().equals("")) {
			sm.subTask("Finding super-class");
			template += " extends " + superclass;
		
			if (index_it != null) {
				SVDBFindByName finder = new SVDBFindByName(index_it);
				List<ISVDBItemBase> result = finder.findItems(superclass, SVDBItemType.ClassDecl);
				if (result.size() > 0 && result.get(0).getType() == SVDBItemType.ClassDecl) {
					superclass_decl = (SVDBClassDecl)result.get(0);
				}
			}
		}
		sm.worked(25);
		
		if (superclass_decl != null) {
			if (superclass_decl.getParameters() != null && 
					superclass_decl.getParameters().size() > 0) {
				template += " #(";
				List<SVDBModIfcClassParam> params = superclass_decl.getParameters(); 
				for (int i=0; i<params.size(); i++) {
					template += params.get(i).getName();
					if (i+1 < params.size()) {
						template += ", ";
					}
				}
				template += ")";
			}
		}
		template += ";\n";
		
		if (implement_new) {
			sm.subTask("Setting up constructor");
			SVDBTask new_func = null;
			if (superclass_decl != null) {
				for (ISVDBChildItem it : superclass_decl.getChildren()) {
					if (it.getType() == SVDBItemType.Function && 
							it instanceof ISVDBNamedItem &&
							((ISVDBNamedItem)it).getName().equals("new")) {
						new_func = (SVDBTask)it;
						break;
					}
				}
			}
			
			if (new_func != null) {
				if (new_func.getParams() != null && 
						new_func.getParams().size() > 0) {
					List<SVDBParamPortDecl> params = new_func.getParams();
					template += "\n";
					template += "function new(";
					
					for (int i=0; i<params.size(); i++) {
						SVDBParamPortDecl p = params.get(i);
						template += p.getTypeName() + " ";
						/*
						for (int j=0; j<p.getVarList().size(); j++) {
							template += p.getVarList().get(j).getName();
							if (j+1 < p.getVarList().size()) {
								template += ", ";
							}
						}
						 */
						for (ISVDBChildItem c : p.getChildren()) {
							template += ((SVDBVarDeclItem)c).getName();
							template += ", ";
						}
					}
					if (template.endsWith(", ")) {
						template = template.substring(0, template.length()-2);
					}
					template += ");\n";

					template += "super.new(";
					for (int i=0; i<params.size(); i++) {
						SVDBParamPortDecl p = params.get(i);
						for (ISVDBChildItem c : p.getChildren()) {
							template += ((SVDBVarDeclItem)c).getName();
							
							template += ", ";
						}
					}
					
					if (template.endsWith(", ")) {
						template = template.substring(0, template.length()-2);
					}
					template += ");\n";
				} else {
					template += "\n";
					template += "function new();\n";
				}
			} else {
				template += "\n";
				template += "function new();\n";
			}
			template += "\n";
			template += "endfunction\n";
			
		}
		sm.worked(25);
		
		template += "\n\n";
		template += "endclass\n";
		
		template += 
			"\n";

		template += "${file_footer}\n";
		
		template = fTagProc.process(template);
		
		sm.subTask("Indenting content");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(new StringBuilder(template)));
		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		indenter.init(scanner);
		final StringInputStream in = new StringInputStream(indenter.indent());
		
		sm.worked(25);
		
		try {
			if (file_path.exists()) {
				file_path.setContents(in, true, true, new NullProgressMonitor());
			} else {
				file_path.create(in, true, new NullProgressMonitor());
			}
		} catch (CoreException e) {}
		
		sm.done();
	}
	
}
