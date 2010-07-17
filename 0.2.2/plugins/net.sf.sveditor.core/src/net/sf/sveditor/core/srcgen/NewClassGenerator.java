package net.sf.sveditor.core.srcgen;

import java.util.List;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.StringTextScanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class NewClassGenerator {
	
	public void generate(
			ISVDBIndexIterator	index_it,
			final IFile			file_path,
			String				clsname,
			String				superclass,
			boolean				implement_new,
			IProgressMonitor	monitor) {
		String subst_filename = "";
		
		if (monitor == null) {
			monitor = new NullProgressMonitor();
		}
		monitor.beginTask("Creating class", 100);
		
		subst_filename = SVCharacter.toSVIdentifier(file_path.getName());
		
		String template =
			"/****************************************************************************\n" +
			" * " + file_path.getName() + "\n" +
			" ****************************************************************************/\n" +
			"`ifndef INCLUDED_" + subst_filename + "\n" +
			"`define INCLUDED_" + subst_filename + "\n" +
			"\n";
		
		template += "class " + clsname;

		SVDBModIfcClassDecl superclass_decl = null;
		if (superclass != null && 
				!superclass.trim().equals("")) {
			monitor.subTask("Finding super-class");
			template += " extends " + superclass;
		
			if (index_it != null) {
				SVDBFindByName finder = new SVDBFindByName(index_it);
				List<SVDBItem> result = finder.find(superclass, SVDBItemType.Class);
				if (result.size() > 0 && result.get(0).getType() == SVDBItemType.Class) {
					superclass_decl = (SVDBModIfcClassDecl)result.get(0);
				}
			}
		}
		monitor.worked(25);
		
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
			monitor.subTask("Setting up constructor");
			SVDBTaskFuncScope new_func = null;
			if (superclass_decl != null) {
				for (SVDBItem it : superclass_decl.getItems()) {
					if (it.getType() == SVDBItemType.Function && 
							it.getName().equals("new")) {
						new_func = (SVDBTaskFuncScope)it;
						break;
					}
				}
			}
			
			if (new_func != null) {
				if (new_func.getParams() != null && 
						new_func.getParams().size() > 0) {
					List<SVDBParamPort> params = new_func.getParams();
					template += "\n";
					template += "function new(";
					
					for (int i=0; i<params.size(); i++) {
						SVDBParamPort p = params.get(i);
						template += p.getTypeName() + " " + p.getName();
						
						if (i+1 < params.size()) {
							template += ", ";
						}
					}
					template += ");\n";

					template += "super.new(";
					for (int i=0; i<params.size(); i++) {
						SVDBParamPort p = params.get(i);
						template += p.getName();
						
						if (i+1 < params.size()) {
							template += ", ";
						}
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
		monitor.worked(25);
		
		template += "\n\n";
		template += "endclass\n";
		
		template += 
			"\n" +
			"`endif /* INCLUDED_" + subst_filename + " */\n";

		monitor.subTask("Indenting content");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(new StringBuilder(template)));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
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
