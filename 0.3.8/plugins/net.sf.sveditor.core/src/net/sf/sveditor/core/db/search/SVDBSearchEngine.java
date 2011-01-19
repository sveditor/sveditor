/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

import org.eclipse.core.runtime.IProgressMonitor;

/**
 * 
 * @author ballance
 *
 * Searches through the database 
 */
public class SVDBSearchEngine {
	private ISVDBIndexIterator					fSearchContext;
	private SVDBSearchSpecification				fSearchSpec;
	private IProgressMonitor					fProgressMonitor;
	
	public SVDBSearchEngine(ISVDBIndexIterator search_ctxt) {
		fSearchContext = search_ctxt;
	}
	
	public synchronized List<SVDBItem> find(SVDBSearchSpecification spec, IProgressMonitor monitor) {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		fProgressMonitor = monitor;
		
		fSearchSpec = spec;
		
		switch (spec.getSearchType()) {
			case Package:
				if (spec.getSearchUsage() == SVDBSearchUsage.Declaration ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_package_decl(ret);
				}
				if (spec.getSearchUsage() == SVDBSearchUsage.Reference ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_package_refs(ret);
				}
				break;
				
			case Method:
				if (spec.getSearchUsage() == SVDBSearchUsage.Declaration ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_method_decl(ret);
				}
				if (spec.getSearchUsage() == SVDBSearchUsage.Reference ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_method_refs(ret);
				}
				break;
				
			case Type:
				if (spec.getSearchUsage() == SVDBSearchUsage.Declaration ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_type_decl(ret);
				}
				if (spec.getSearchUsage() == SVDBSearchUsage.Reference ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_type_refs(ret);
				}
				break;
				
			case Field:
				if (spec.getSearchUsage() == SVDBSearchUsage.Declaration ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_field_decl(ret);
				}
				if (spec.getSearchUsage() == SVDBSearchUsage.Reference ||
						spec.getSearchUsage() == SVDBSearchUsage.All) {
					find_field_refs(ret);
				}
				break;
		}

		return ret;
	}

	private void find_package_decl(List<SVDBItem> items) {
		ISVDBItemIterator iterator = fSearchContext.getItemIterator();
		
		while (iterator.hasNext(SVDBItemType.PackageDecl)) {
			SVDBItem pkg = iterator.nextItem(SVDBItemType.PackageDecl);
			if (fSearchSpec.match(pkg.getName())) {
				items.add(pkg);
			}
		}
	}
	
	private void find_package_refs(List<SVDBItem> items) {
		ISVDBItemIterator iterator = fSearchContext.getItemIterator();

		System.out.println("[ERROR] find_package_refs not supported");
	}
	
	private void find_type_decl(List<SVDBItem> items) {
		ISVDBItemIterator iterator = fSearchContext.getItemIterator();
		SVDBItemType types[] = new SVDBItemType[] {SVDBItemType.Class, SVDBItemType.Struct, 
				SVDBItemType.Typedef, SVDBItemType.Module};
		
		while (iterator.hasNext(types)) {
			SVDBItem item = iterator.nextItem(types);
			if (item.getType() == SVDBItemType.Typedef) {
				SVDBTypedef td = (SVDBTypedef)item;
				if (td.getTypeInfo().getDataType() != SVDBDataType.Struct) {
					continue;
				}
			}
			if (fSearchSpec.match(item.getName())) {
				items.add(item);
			}
		}
	}
	
	private void find_type_refs(List<SVDBItem> items) {
		ISVDBItemIterator iterator = fSearchContext.getItemIterator();
		SVDBItemType types[] = new SVDBItemType[] {SVDBItemType.VarDecl, SVDBItemType.ModIfcInst}; 
		
		while (iterator.hasNext(types)) {
			SVDBItem item = iterator.nextItem(types);
			String match_name = "";
			if (item.getType() == SVDBItemType.VarDecl) {
				SVDBVarDeclItem decl = (SVDBVarDeclItem)item;
				match_name = decl.getTypeInfo().getName();
			} else if (item.getType() == SVDBItemType.ModIfcInst) {
				SVDBModIfcInstItem inst = (SVDBModIfcInstItem)item;
				
				match_name = inst.getTypeName(); 
			}
			if (fSearchSpec.match(match_name)) {
				items.add(item);
			}
		}
	}
	
	private void find_method_decl(List<SVDBItem> items) {
		ISVDBItemIterator iterator = fSearchContext.getItemIterator();
		SVDBItemType types[] = new SVDBItemType[] {SVDBItemType.Function, SVDBItemType.Task};
		
		while (iterator.hasNext(types)) {
			SVDBItem item = iterator.nextItem();
			String name = item.getName();
			
			// Trim away the scope
			if (name.indexOf("::") != -1) {
				name = name.substring(name.lastIndexOf("::")+2);
			}
			if (fSearchSpec.match(name)) {
				items.add(item);
			}
		}
	}
	
	private void find_method_refs(List<SVDBItem> items) {
		
	}
	
	private void find_field_decl(List<SVDBItem> items) {
		ISVDBItemIterator iterator = fSearchContext.getItemIterator();
		SVDBItemType types[] = new SVDBItemType[] {SVDBItemType.VarDecl, SVDBItemType.ModIfcInst};

		while (iterator.hasNext(types)) {
			SVDBItem item = iterator.nextItem();
			String name = item.getName();
			
			if (fSearchSpec.match(name)) {
				items.add(item);
			}
		}
	}
	
	private void find_field_refs(List<SVDBItem> items) {
		
	}
}
