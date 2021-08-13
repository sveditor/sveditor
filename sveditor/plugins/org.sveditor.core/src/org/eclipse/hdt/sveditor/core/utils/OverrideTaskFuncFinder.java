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
package org.eclipse.hdt.sveditor.core.utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindSuperClass;

public class OverrideTaskFuncFinder {
	
	public List<Tuple<SVDBTask, SVDBTask>> find(SVDBFile file, ISVDBIndexIterator index_it) {
		List<Tuple<SVDBTask, SVDBTask>> ret = new ArrayList<Tuple<SVDBTask,SVDBTask>>();
				
		SVDBFindSuperClass super_finder = new SVDBFindSuperClass(index_it);
		List<SVDBClassDecl> classes = new ArrayList<SVDBClassDecl>();
	
		if (file.getLocation() == -1) {
			return ret;
		}
		
		collectClasses(classes, SVDBLocation.unpackFileId(file.getLocation()), file);
		
		for (SVDBClassDecl cls : classes) {
			SVDBClassDecl super_cls = super_finder.find(cls);
			
			if (super_cls != null) {
				Set<String> processed_classes = new HashSet<String>();
				Set<SVDBTask> super_methods = new HashSet<SVDBTask>();
				List<SVDBTask> override_tf = new ArrayList<SVDBTask>();
				collectSuperClassMethods(processed_classes, super_methods, super_finder, super_cls);
				
				collectOverrideMethods(cls, super_methods, override_tf);
				
				// Apply override annotations
				for (SVDBTask tf : override_tf) {
					
					SVDBTask target_t = null;
					for (SVDBTask ti : super_methods) {
						if (ti.getName().equals(tf.getName())) {
							target_t = ti;
							break;
						}
					}
					
					if (target_t == null) {
						// unexpected
						continue;
					}
					
					ret.add(new Tuple<SVDBTask, SVDBTask>(tf, target_t));
				}
			}			
		}
		
		return ret;
	}
	
	private void collectClasses(
			List<SVDBClassDecl> 		classes, 
			int							file_id,
			ISVDBChildParent 			scope) {
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (ci.getType() == SVDBItemType.ClassDecl) {
				if (ci.getLocation() != -1 && 
						SVDBLocation.unpackFileId(ci.getLocation()) == file_id) {
					classes.add((SVDBClassDecl)ci);
				}
			} else if (ci.getType() == SVDBItemType.PackageDecl ||
					ci.getType() == SVDBItemType.ModuleDecl ||
					ci.getType() == SVDBItemType.InterfaceDecl ||
					ci.getType() == SVDBItemType.ProgramDecl) {
				if (ci.getLocation() != -1 && SVDBLocation.unpackFileId(ci.getLocation()) == file_id) {
					collectClasses(classes, file_id, (ISVDBChildParent)ci);
				}
			}
		}
	}
	
	private void collectSuperClassMethods(
			Set<String>				processed_classes, // avoid accidental infinite recursion
			Set<SVDBTask>			super_methods,
			SVDBFindSuperClass		super_class_finder,
			SVDBClassDecl			cls) {

		processed_classes.add(cls.getName());
		for (ISVDBChildItem ci : cls.getChildren()) {
			// Look for tasks/functions here
			if (ci.getType() == SVDBItemType.Function ||
					ci.getType() == SVDBItemType.Task) {
				boolean found = false;
				String name = SVDBItem.getName(ci);
				
				if (!name.equals("new")) {
					for (SVDBTask t : super_methods) {
						if (t.getName().equals(name)) {
							found = true;
							break;
						}
					}

					if (!found) {
						super_methods.add((SVDBTask)ci);
					}
				}
			}
		}
		
		SVDBClassDecl super_cls = super_class_finder.find(cls);
		
		if (super_cls != null) {
			if (!processed_classes.contains(super_cls.getName())) {
				collectSuperClassMethods(processed_classes, super_methods, super_class_finder, super_cls);
			}
		}
	}

	private void collectOverrideMethods(
			SVDBClassDecl	 		cls,
			Set<SVDBTask>			super_methods,
			List<SVDBTask>			override_tf) {
		for (ISVDBChildItem ci : cls.getChildren()) {
			if (ci.getType() == SVDBItemType.Task || ci.getType() == SVDBItemType.Function) {
				// 
				SVDBTask t = (SVDBTask)ci;
				boolean found = false;
				for (SVDBTask ti : super_methods) {
					if (ti.getName().equals(t.getName())) {
						found = true;
						break;
					}
				}
				if (found) {
					override_tf.add(t);
				}
			}
		}
	}

}
