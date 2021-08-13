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


package org.sveditor.core.db.search;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sveditor.core.Tuple;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.ISVDBScopeItem;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBFunction;
import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.SVDBParamValueAssign;
import org.sveditor.core.db.SVDBParamValueAssignList;
import org.sveditor.core.db.SVDBTask;
import org.sveditor.core.db.SVDBTypeInfoBuiltin;
import org.sveditor.core.db.SVDBTypeInfoUserDef;
import org.sveditor.core.db.index.ISVDBIndexIterator;
import org.sveditor.core.db.stmt.SVDBParamPortDecl;
import org.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.sveditor.core.scanner.SVKeywords;

/**
 * Find a named class given its parameterization 
 * 
 * @author ballance
 *
 */
public class SVDBFindParameterizedClass {
	private ISVDBIndexIterator									fIndexIt;
	private Set<Tuple<SVDBClassDecl, SVDBTypeInfoUserDef>>		fParamClassCache;
	private SVDBFindNamedClass									fFindNamedClass;
	
	public SVDBFindParameterizedClass(ISVDBIndexIterator it) {
		fIndexIt = it;
		fParamClassCache = new HashSet<Tuple<SVDBClassDecl,SVDBTypeInfoUserDef>>();
		fFindNamedClass = new SVDBFindNamedClass(fIndexIt);
	}
	
	
	public SVDBClassDecl find(SVDBTypeInfoUserDef type_info) {
		SVDBClassDecl ret = null;
		
		// First, look through the hash
		for (Tuple<SVDBClassDecl, SVDBTypeInfoUserDef> cls_t : fParamClassCache) {
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
			List<SVDBClassDecl> result = fFindNamedClass.findItem(type_info.getName());
			
			if (result.size() > 0) {
				ret = specialize(result.get(0), type_info);
				fParamClassCache.add(
						new Tuple<SVDBClassDecl, SVDBTypeInfoUserDef>(ret, type_info));
			}
		}
		
		return ret;
	}

	private SVDBClassDecl specialize(
			SVDBClassDecl 			decl,
			SVDBTypeInfoUserDef		type_info) {
		Map<String, String> param_map = new HashMap<String, String>();
		SVDBClassDecl s_decl = (SVDBClassDecl)decl.duplicate();
		
		SVDBParamValueAssignList param_list = type_info.getParameters();
		for (int i=0; i<decl.getParameters().size(); i++) {
			String p_name = decl.getParameters().get(i).getName();
			// TODO:
			SVDBParamValueAssign assign = param_list.getParameters().get(i);
			String p_val  = ""; 
			if (assign.getValue() == null) {
				System.out.println("[ERROR] parameter \"" + assign.getName() + "\" has null value");
			} else {
				p_val = assign.getValue().toString();
			}
			param_map.put(p_name, p_val);
		}
		
		specialize_int(s_decl, param_map);
		
		return s_decl;
	}
	
	private void specialize_int(
			ISVDBItemBase 				item,
			Map<String, String>		param_map) {
		switch (item.getType()) {
			case ClassDecl:
				specialize_cls((SVDBClassDecl)item, param_map);
				break;
				
			case Task:
			case Function:
				specialize_tf((SVDBTask)item, param_map);
				break;
				
			case VarDeclStmt: {
				specialize_var_decl((SVDBVarDeclStmt)item, param_map);
				} break;
			
			default:
				if (item instanceof ISVDBScopeItem) {
					ISVDBScopeItem scope = (ISVDBScopeItem)item;
					for (ISVDBItemBase it : scope.getItems()) {
						specialize_int(it, param_map);
					}
				}
				break;
		}
	}
	
	private void specialize_tf(
			SVDBTask 		tf, 
			Map<String, String>		param_map) {
		if (tf.getType() == SVDBItemType.Function) {
			SVDBFunction func = (SVDBFunction)tf;
			if (param_map.containsKey(((SVDBFunction)tf).getReturnType())) {
				String type = param_map.get(func.getReturnType().getName());
				
				if (SVKeywords.isBuiltInType(type)) {
					SVDBTypeInfoBuiltin ret_type = 
						new SVDBTypeInfoBuiltin(type);
					func.setReturnType(ret_type);
				} else {
					SVDBTypeInfoUserDef ret_type = 
						new SVDBTypeInfoUserDef(type);
					func.setReturnType(ret_type);
				}
			}
		}
		
		for (SVDBParamPortDecl p : tf.getParams()) {
			if (param_map.containsKey(p.getTypeInfo().getName())) {
				p.getTypeInfo().setName(
						param_map.get(p.getTypeInfo().getName()));
			}
		}
	}
	
	private void specialize_cls(
			SVDBClassDecl			cls,
			Map<String, String>		param_map) {
		if (cls.getSuperClass() != null && cls.getSuperClass().getParamAssignList() != null) {
			for (SVDBParamValueAssign p : cls.getSuperClass().getParamAssignList().getParameters()) {
				if (param_map.containsKey(p.getName())) {
					p.setName(param_map.get(p.getName()));
				}
			}
		}

		/** TODO:
		if (cls.isParameterized()) {
			for (SVDBModIfcClassParam p : cls.getParameters()) {
				if (param_map.containsKey(p.getName())) {
					p.setName(param_map.get(p.getName()));
				}
			}
		}
		 */
		
		for (ISVDBItemBase it : cls.getChildren()) {
			specialize_int(it, param_map);
		}
	}
			
	
	private void specialize_var_decl(
			SVDBVarDeclStmt			var_decl,
			Map<String, String>		param_map) {
		// Only specialize non-parameterized types. Parameterized types
		// will be parameterized on-demand
		if (var_decl.getTypeInfo().getType() == SVDBItemType.TypeInfoUserDef) {
			SVDBTypeInfoUserDef cls = (SVDBTypeInfoUserDef)var_decl.getTypeInfo(); 
			if (cls.getParameters() == null || cls.getParameters().getParameters().size() == 0) {
				if (param_map.containsKey(var_decl.getTypeInfo().getName())) {
					var_decl.getTypeInfo().setName(param_map.get(
							var_decl.getTypeInfo().getName()));
				}
			}
		}
	}

}
