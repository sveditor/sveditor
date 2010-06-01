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

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.scanner.SVKeywords;

/**
 * Find a named class given its parameterization 
 * 
 * @author ballance
 *
 */
public class SVDBFindParameterizedClass {
	private ISVDBIndexIterator										fIndexIt;
	private Set<Tuple<SVDBModIfcClassDecl, SVDBTypeInfoUserDef>>	fParamClassCache;
	private SVDBFindNamedModIfcClassIfc								fFinder;
	
	public SVDBFindParameterizedClass(ISVDBIndexIterator it) {
		fIndexIt = it;
		fParamClassCache = new HashSet<Tuple<SVDBModIfcClassDecl,SVDBTypeInfoUserDef>>();
		fFinder = new SVDBFindNamedModIfcClassIfc(fIndexIt);
	}
	
	
	public SVDBModIfcClassDecl find(SVDBTypeInfoUserDef type_info) {
		SVDBModIfcClassDecl ret = null;
		
		// First, look through the hash
		for (Tuple<SVDBModIfcClassDecl, SVDBTypeInfoUserDef> cls_t : fParamClassCache) {
			if (cls_t.first().getName().equals(type_info.getName())) {
				SVDBTypeInfoUserDef ti_t = cls_t.second();
				SVDBParamValueAssignList type_params = type_info.getParameters();
				SVDBParamValueAssignList ti_params = ti_t.getParameters();
				
				if (type_params == null && ti_params == null) {
					ret = cls_t.first();
					break;
				} else if (type_params != null && ti_params != null) {
					if (type_params.getParameters().size() == ti_params.getParameters().size()) {
						boolean match = true;

						for (int i=0; i<type_params.getParameters().size(); i++) {
							SVDBParamValueAssign p1 = type_params.getParameters().get(i);
							SVDBParamValueAssign p2 = ti_params.getParameters().get(i);

							if (!p1.getName().equals(p2.getName())) {
								match = false;
								break;
							}
						}

						if (match ) {
							ret = cls_t.first();
							break;
						}
					}
				}

			}
		}
		
		if (ret == null) {
			List<SVDBModIfcClassDecl> result = fFinder.find(type_info.getName());
			
			if (result.size() > 0) {
				ret = specialize(result.get(0), type_info);
				fParamClassCache.add(
						new Tuple<SVDBModIfcClassDecl, SVDBTypeInfoUserDef>(ret, type_info));
			}
		}
		
		return ret;
	}

	private SVDBModIfcClassDecl specialize(
			SVDBModIfcClassDecl 	decl,
			SVDBTypeInfoUserDef		type_info) {
		Map<String, String> param_map = new HashMap<String, String>();
		SVDBModIfcClassDecl s_decl = (SVDBModIfcClassDecl)decl.duplicate();
		
		SVDBParamValueAssignList param_list = type_info.getParameters();
		for (int i=0; i<decl.getParameters().size(); i++) {
			String p_name = decl.getParameters().get(i).getName();
			String p_val  = param_list.getParameters().get(i).getValue();
			param_map.put(p_name, p_val);
		}
		
		specialize_int(s_decl, param_map);
		
		return s_decl;
	}
	
	private void specialize_int(
			SVDBItem 				item,
			Map<String, String>		param_map) {
		switch (item.getType()) {
			case Class:
				specialize_cls((SVDBModIfcClassDecl)item, param_map);
				break;
				
			case Task:
			case Function:
				specialize_tf((SVDBTaskFuncScope)item, param_map);
				break;
				
			case VarDecl:
				specialize_var_decl((SVDBVarDeclItem)item, param_map);
				break;
			
			default:
				if (item instanceof SVDBScopeItem) {
					SVDBScopeItem scope = (SVDBScopeItem)item;
					for (SVDBItem it : scope.getItems()) {
						specialize_int(it, param_map);
					}
				}
				break;
		}
	}
	
	private void specialize_tf(
			SVDBTaskFuncScope 		tf, 
			Map<String, String>		param_map) {
		if (tf.getType() == SVDBItemType.Function) {
			if (param_map.containsKey(tf.getReturnType())) {
				String type = param_map.get(tf.getReturnType().getName());
				
				if (SVKeywords.isBuiltInType(type)) {
					SVDBTypeInfoBuiltin ret_type = 
						new SVDBTypeInfoBuiltin(type);
					tf.setReturnType(ret_type);
				} else {
					SVDBTypeInfoUserDef ret_type = 
						new SVDBTypeInfoUserDef(type);
					tf.setReturnType(ret_type);
				}
			}
		}
		
		for (SVDBTaskFuncParam p : tf.getParams()) {
			if (param_map.containsKey(p.getTypeInfo().getName())) {
				p.getTypeInfo().setName(
						param_map.get(p.getTypeInfo().getName()));
			}
		}
	}
	
	private void specialize_cls(
			SVDBModIfcClassDecl			cls,
			Map<String, String>			param_map) {
		if (cls.getSuperParameters() != null) {
			for (SVDBModIfcClassParam p : cls.getSuperParameters()) {
				if (param_map.containsKey(p.getName())) {
					p.setName(param_map.get(p.getName()));
				}
			}
		}

		if (cls.isParameterized()) {
			for (SVDBModIfcClassParam p : cls.getParameters()) {
				if (param_map.containsKey(p.getName())) {
					p.setName(param_map.get(p.getName()));
				}
			}
		}
		
		for (SVDBItem it : cls.getItems()) {
			specialize_int(it, param_map);
		}
	}
			
	
	private void specialize_var_decl(
			SVDBVarDeclItem			var_decl,
			Map<String, String>		param_map) {
		// Only specialize non-parameterized types. Parameterized types
		// will be parameterized on-demand
		SVDBTypeInfoUserDef cls = (SVDBTypeInfoUserDef)var_decl.getTypeInfo(); 
		if (cls.getParameters() == null) {
			if (param_map.containsKey(var_decl.getTypeInfo().getName())) {
				var_decl.getTypeInfo().setName(param_map.get(
						var_decl.getTypeInfo().getName()));
			}
		}
	}

}
