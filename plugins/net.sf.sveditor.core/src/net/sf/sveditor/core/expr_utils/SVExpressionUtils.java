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


package net.sf.sveditor.core.expr_utils;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoStruct;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import net.sf.sveditor.core.db.search.SVDBFindByNameInScopes;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.search.SVDBFindIncludedFile;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.search.SVDBFindParameterizedClass;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.db.search.SVDBFindVarsByNameInScopes;
import net.sf.sveditor.core.db.search.SVDBPackageItemFinder;
import net.sf.sveditor.core.db.search.SVDBStructFieldFinder;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.expr_utils.SVExprContext.ContextType;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;

/**
 * SVExpressionUtils
 * 
 * Utility class that textually processes SV expressions. Used both by
 * content-assist and by cross-linking
 * @author ballance
 *
 */
public class SVExpressionUtils {
	
	private boolean 						fDebugEn = true;
	private LogHandle						fLog;
	private ISVDBFindNameMatcher			fNameMatcher;
	private SVDBFindDefaultNameMatcher		fDefaultMatcher;
	private SVDBFindParameterizedClass 		fParamClassFinder;

	public SVExpressionUtils(ISVDBFindNameMatcher matcher) {
		fLog = LogFactory.getLogHandle("SVExpressionUtils");
		fNameMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
	}
	
	public void setMatcher(ISVDBFindNameMatcher matcher) {
		fNameMatcher = matcher;
	}
	
	public synchronized List<ISVDBItemBase> findItems(
			ISVDBIndexIterator	index_it,
			ISVDBScopeItem		active_scope,
			SVExprContext		expr_ctxt,
			boolean				match_prefix) {
		fParamClassFinder = new SVDBFindParameterizedClass(index_it);
		return findItems(index_it, active_scope, expr_ctxt, match_prefix, 0);
	}
	
	private List<ISVDBItemBase> findItems(
			ISVDBIndexIterator	index_it,
			ISVDBScopeItem		active_scope,
			SVExprContext		expr_ctxt,
			boolean				match_prefix,
			int					max_matches) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		fLog.debug("--> findItems(active_scope=\"" + 
				((active_scope != null)?((ISVDBNamedItem)active_scope).getName():null) + "\" " +
				" root=\"" + expr_ctxt.fRoot + "\" trigger=\"" + expr_ctxt.fTrigger +
				"\" leaf=\"" + expr_ctxt.fLeaf + "\" match_prefix=" + match_prefix + ")");

		if (expr_ctxt.fTrigger != null && !expr_ctxt.fTrigger.equals("=")) {
			if (expr_ctxt.fTrigger.equals("`")) {
				findMacroItems(expr_ctxt, index_it, max_matches, match_prefix, ret);
			} else {
				findTriggeredItems(expr_ctxt.fRoot, expr_ctxt.fTrigger, 
						expr_ctxt.fLeaf, active_scope, index_it, max_matches, 
						match_prefix, ret);
			}
		} else {
			// Trigger is null or '='
			if (expr_ctxt.fType == ContextType.Import) {
				SVDBFindByName finder = new SVDBFindByName(index_it, fNameMatcher);
				ret.addAll(finder.find(expr_ctxt.fLeaf, SVDBItemType.PackageDecl));
			} else {
				findUntriggeredItems(expr_ctxt.fRoot, expr_ctxt.fTrigger,
						expr_ctxt.fLeaf, active_scope, index_it, 
						max_matches, match_prefix, ret);
			}
		}

		fLog.debug("<-- findItems(root=\"" + expr_ctxt.fRoot + "\" trigger=\"" + 
				expr_ctxt.fTrigger + "\" leaf=\"" + expr_ctxt.fLeaf + 
				"\" match_prefix=" + match_prefix + ") returns " + ret.size() + " results");
		return ret;
	}
	
	private void findMacroItems(
			SVExprContext 			expr_ctxt,
			ISVDBIndexIterator		index_it,
			int						max_matches,
			boolean					match_prefix,
			List<ISVDBItemBase> 	ret) {
		
		if (expr_ctxt.fRoot != null && expr_ctxt.fRoot.equals("include")) {
			SVDBFindIncludedFile finder = new SVDBFindIncludedFile(
					index_it, fNameMatcher);
			List<SVDBFile> it_l = finder.find(expr_ctxt.fLeaf);

			if (it_l.size() > 0 && (max_matches == 0 || ret.size() < max_matches)) {
				ret.addAll(it_l);
			}
		} else {
			// most likely a macro call
			ISVDBItemIterator it_i = index_it.getItemIterator(new NullProgressMonitor());
			while (it_i.hasNext()) {
				ISVDBItemBase it_t = it_i.nextItem();

				if (it_t.getType() == SVDBItemType.Macro) {
					if (match_prefix) {
						if (expr_ctxt.fLeaf.equals("") || 
								((ISVDBNamedItem)it_t).getName().startsWith(expr_ctxt.fLeaf)) {
							if (max_matches == 0 || (ret.size() < max_matches)) {
								ret.add(it_t);
							} else {
								break;
							}
						}
					} else {
						if (((ISVDBNamedItem)it_t).getName().equals(expr_ctxt.fLeaf)) {
							if (max_matches == 0 || (ret.size() < max_matches)) {
								ret.add(it_t);
							} else {
								break;
							}
						}
					}
				}
			}
		}
	}
	
	private void findTriggeredItems(
			String					root,
			String					trigger,
			String					leaf,
			ISVDBScopeItem			active_scope,
			ISVDBIndexIterator		index_it,
			int						max_matches,
			boolean					match_prefix,
			List<ISVDBItemBase> 	ret) {
		debug("--> findTriggeredItems");
		fLog.debug("Expression is triggered expression");
		List<SVDBItem> pre_trigger = processPreTriggerPortion(
				index_it, active_scope, root, !match_prefix);
		
		if (pre_trigger != null && pre_trigger.size() > 0) {
			SVDBItem it_t = pre_trigger.get(pre_trigger.size()-1);
			
			fLog.debug("Using " + it_t.getType() + " " + 
					it_t.getName() + " as search base");

			if (it_t.getType() == SVDBItemType.Class || 
					it_t.getType() == SVDBItemType.Struct ||
					it_t.getType() == SVDBItemType.Covergroup ||
					it_t.getType() == SVDBItemType.Coverpoint) {
				SVDBFindByNameInClassHierarchy finder_h = 
					new SVDBFindByNameInClassHierarchy(index_it, fNameMatcher);
				List<ISVDBItemBase> fields = finder_h.find((SVDBScopeItem)it_t, leaf);
				
				fLog.debug("Find Named Field returns " + fields.size() + " results");
				for (ISVDBItemBase it : fields) {
					fLog.debug("    " + it.getType() + " " + ((ISVDBNamedItem)it).getName());
				}

				if (fields.size() > 0) {
					if (max_matches == 0 || (ret.size() < max_matches)) {
						ret.addAll(fields);
					}
				}
			} else if (it_t.getType() == SVDBItemType.PackageDecl) {
				SVDBPackageItemFinder finder_p = new SVDBPackageItemFinder(
						index_it, fNameMatcher);
				ret.addAll(finder_p.find((SVDBPackageDecl)it_t, leaf));
			} else if (it_t.getType() == SVDBItemType.TypeInfo) {
				SVDBTypeInfo ti = (SVDBTypeInfo)it_t;
				if (ti.getDataType() == SVDBDataType.Struct) {
					SVDBTypeInfoStruct struct = (SVDBTypeInfoStruct)ti;
					SVDBStructFieldFinder finder = new SVDBStructFieldFinder(fNameMatcher);
					ret.addAll(finder.find(struct, leaf));
				}
			} else {
				fLog.debug("Target type is " + it_t.getType() + " -- cannot search");
			}
		}
	}
	
	private void findUntriggeredItems(
			String					root,
			String					trigger,
			String					leaf,
			ISVDBScopeItem			active_scope,
			ISVDBIndexIterator		index_it,
			int						max_matches,
			boolean					match_prefix,
			List<ISVDBItemBase> 	ret) {

		fLog.debug("Looking for un-triggered identifier \"" + leaf + "\"");
		List<ISVDBItemBase> result = null;

		SVDBFindByNameInClassHierarchy finder_h =
			new SVDBFindByNameInClassHierarchy(index_it, fNameMatcher);

		result = finder_h.find(active_scope, leaf);

		if (result.size() > 0) {
			for (int i=0; i<result.size(); i++) {
				boolean add = true;
				
				if (trigger != null && trigger.equals("=") &&
						"new".startsWith(leaf)) {
					// This is possibly a call to 'new'. We'll add
					// a proposal for this later based on the base type
					if (result.get(i).getType() == SVDBItemType.Function &&
							((ISVDBNamedItem)result.get(i)).getName().equals("new")) {
						add = false;
					}
				}
				
				if (max_matches > 0 && ret.size() >= max_matches) {
					add = false;
				}
				
				if (add) {
					ret.add(result.get(i));
				}
			}
		}

		// Try type names
		SVDBFindNamedModIfcClassIfc finder_cls =
			new SVDBFindNamedModIfcClassIfc(index_it, fNameMatcher);

		List<SVDBModIfcClassDecl> cl_l = finder_cls.find(leaf);

		if (cl_l.size() > 0) {
			fLog.debug("Global type search for \"" + leaf + 
					"\" returned " + cl_l.size());
			for (SVDBModIfcClassDecl cl : cl_l) {
				fLog.debug("    " + cl.getType() + " " + cl.getName());
			}
			if (max_matches == 0 || ret.size() < max_matches) {
				ret.addAll(cl_l);
			}
		} else {
			fLog.debug("Global class find for \"" + leaf + 
			"\" returned no results");
		}

		// Try global task/function
		SVDBFindByName finder_tf = new SVDBFindByName(index_it, fNameMatcher);

		List<ISVDBItemBase> it_l = finder_tf.find(leaf,
				SVDBItemType.Task, SVDBItemType.Function, SVDBItemType.Typedef,
				SVDBItemType.PackageDecl);
		
		// Remove any definitions of extern tasks/functions, 
		// since the name prefix was incorrectly matched
		for (int i=0; i<it_l.size(); i++) {
			if (it_l.get(i).getType() == SVDBItemType.Function || 
					it_l.get(i).getType() == SVDBItemType.Task) {
				SVDBTaskFuncScope tf = (SVDBTaskFuncScope)it_l.get(i);
				if ((tf.getAttr() & IFieldItemAttr.FieldAttr_Extern) == 0 &&
						tf.getName().contains("::")) {
					it_l.remove(i);
					i--;
				}
				
				// Do not include tasks/functions unless they are completely
				// global or members of a package
				ISVDBScopeItem scope_t = tf;
				while (scope_t != null && 
						scope_t.getType() != SVDBItemType.Class &&
						scope_t.getType() != SVDBItemType.Module) {
					scope_t = scope_t.getParent();
				}

				if (scope_t != null && 
						(scope_t.getType() == SVDBItemType.Class ||
						scope_t.getType() == SVDBItemType.Module)) {
					it_l.remove(i);
					i--;
				}
			}
		}
		
		if (it_l != null && it_l.size() > 0) {
			fLog.debug("Global find-by-name \"" + leaf + "\" returned:");
			for (ISVDBItemBase it : it_l) {
				fLog.debug("    " + it.getType() + " " + ((ISVDBNamedItem)it).getName());
			}

			if (max_matches == 0 || (ret.size() < max_matches)) {
				ret.addAll(it_l);
			}
		} else {
			fLog.debug("Global find-by-name \"" + leaf + 
			"\" returned no results");
		}
		
		// Special case: If this is a constructor call, then do a 
		// context lookup on the LHS
		if (root != null && trigger != null && trigger.equals("=") &&
				leaf != null && "new".startsWith(leaf)) {
			fLog.debug("Looking for new in root=" + root);
			findTriggeredItems(root, "=", "new", active_scope, 
					index_it, max_matches, false, ret);
		}
	}
	
	/**
	 * Scans backwards (from idx) in the text viewer 
	 * to extract a SystemVerilog reference expression.
	 * 
	 * It is expected that all elements of the expression
	 * will be joined with '.' or '::'
	 * 
	 * eg: a.b().c::d;
	 * 
	 * if search_forward is true, then 
	 * 
	 * @param viewer
	 * @param idx
	 * @param search_forward
	 * @return
	 */
	public String extractPreTriggerPortion(IBIDITextScanner doc) {
		StringBuffer tmp = new StringBuffer();
		int last_nws_ch = -1;
		String end_match[] = { 
				"dne", // end
				"nigeb", // begin
				";",
				"=",
				"*/",
				"//"};
		
		doc.setScanFwd(false);
		int ch = -1;

		do {
			
			// Skip whitespace
			while ((ch = doc.get_ch()) != -1 && Character.isWhitespace(ch)) {
				tmp.append((char)ch);
			}

			if (ch == -1) {
				break;
			}

			if (ch == '(' || ch == ',') {
				break;
			} else if (ch == ')') {
				if (last_nws_ch != '.' && last_nws_ch != ':'
					&& last_nws_ch != -1) {
					break;
				}

				int matchLevel = 1;

				tmp.append((char) ch);

				// Otherwise, skip matching braces
				while (matchLevel > 0 && (ch = doc.get_ch()) != -1) {
					// next char
					if (ch == ')') {
						matchLevel++;
					} else if (ch == '(') {
						matchLevel--;
					}
					tmp.append((char) ch);
				}
			} else {
				tmp.append((char) ch);
			}

			last_nws_ch = ch;

			String end = null;
			for (int i = 0; i < end_match.length; i++) {
				if (tmp.toString().endsWith(end_match[i])) {
					tmp.setLength(tmp.length() - end_match[i].length());
					debug("matched \"" + end_match[i] + "\"");
					end = end_match[i];
					break;
				}
			}

			if (end != null) {
				if (end.equals("//")) {
					// We scanned to the beginning of a comment. 
					// backtrack now
					int i=tmp.length();
					while (i>0 && tmp.charAt(i-1) != '\n') {
						i--;
					}
					tmp.setLength(i);
				}
				break;
			}
		} while (ch != -1);

		return tmp.reverse().toString().trim();
	}
	
	
	/**
	 * Process the pre-trigger portion of a context string
	 * 
	 * @param searcher
	 * @param context
	 * @param preTrigger
	 * @return
	 */
	private List<SVDBItem> processPreTriggerPortion(
			ISVDBIndexIterator			index_it,
			ISVDBScopeItem				context,
			String						preTrigger,
			boolean						allowNonClassLastElem) {
		List<SVDBItem> item_list = new ArrayList<SVDBItem>();
		ITextScanner scanner = new StringTextScanner(preTrigger);
		
		debug("--> processPreTriggerPortion() preTrigger=" + preTrigger);
		
		int ret = processPreTriggerPortion(scanner, null, item_list, 
				index_it, context, allowNonClassLastElem);
		
		if (ret == -1) {
			return null;
		} else {
			return item_list;
		}
	}

	/**
	 * 
	 * The procedure here is pretty simple:
	 * - Read an identifier
	 *   - Determine whether it is a function, variable, or cast
	 *       - If a cast, lookup the type
	 *       - else if first lookup, lookup starting from current scope 
	 *           and look through hierarchy
	 *       - else lookup id in last-located type  
	 *       
	 * TODO: need to resolve parameterized types
     *
	 * @param idx
	 * @param preceeding_activator
	 * @param item_list
	 * @param searcher
	 * @param context
	 * @param preTrigger
	 * @param resolveFinalReturnType -- 
	 *    Causes the algorithm to resolve the return type of the
	 *    final function in the string
	 * @return
	 */
	private int processPreTriggerPortion(
			ITextScanner				scanner,
			String						preceeding_activator,
			List<SVDBItem>				item_list,
			ISVDBIndexIterator			index_it,
			ISVDBScopeItem				context,
			boolean						resolveFinalReturnType) {
		String id = null;
		int ret = 0;
		
		debug("--> processPreTriggerPortion(preceeding_activator=" + preceeding_activator + ")");
		// Need to make some changes to track the preceeding character, not the
		// next. For example, if the preceeding character was '.', then we should
		// look for id() within typeof(ret.item)
		int ch;
		while ((ch = scanner.get_ch()) != -1) {
			debug("    processPreTriggerPortion: ch=" + (char)ch);

			if (ch == '(') {
				// recursively expand
				ret = processPreTriggerPortion(
						scanner, preceeding_activator, item_list,
						index_it, context, resolveFinalReturnType);
				
				// Give up because the lower-level parser did...
				if (ret == -1) {
					break;
				}
			} else if (ch == '[') {
				ret = processPreTriggerArrayRef(scanner, index_it, item_list);
			} else if (ch == '.') {
				// use the preceeding
				preceeding_activator = ".";
			} else if (ch == ':') {
				int ch2 = scanner.get_ch();
				if (ch2 == ':') {
					preceeding_activator= "::"; 
				} else {
					scanner.unget_ch(ch2);
					// TODO: give up?
					return -1;
				}
			} else if (SVCharacter.isSVIdentifierPart(ch)) {
				id = scanner.readIdentifier(ch);
				
				if (id == null) {
					debug("id==null ch==" + (char)ch);
				}
				
				ret = processPreTriggerId(context, scanner, id, 
						preceeding_activator, resolveFinalReturnType, 
						index_it, item_list);

				// Lookup failed, so bail
				if (ret == -1) {
					debug("    lookup failed -- end processing");
					break;
				}
			} else {
				// TODO: This is actually an error (?)
				fLog.error("CHECK: ch=" + (char)ch + " is this an error?");
				return -1;
			}
		}

		debug("<-- processPreTriggerPortion(preceeding_activator=" + preceeding_activator + ")");
		for (SVDBItem it : item_list) {
			fLog.debug("    " + it.getType() + " " + it.getName());
		}
		return 0;
	}
	
	private int processPreTriggerArrayRef(
			ITextScanner		scanner,
			ISVDBIndexIterator	index_it,
			List<SVDBItem>		item_list) {
		debug("--> processPreTriggerArrayRef: ");
		
		// TODO: This is an array reference. Must find base type of preceeding variable
		scanner.skipPastMatch("[]");
		
		if (item_list.size() > 0) {
			SVDBItem it = item_list.get(item_list.size()-1);
			debug("  last item type=" + it.getType());
			
			if (it.getType() == SVDBItemType.Class) {
				SVDBModIfcClassDecl cls_t = (SVDBModIfcClassDecl)it;
				// cls_t should be the specialized array type. We use the template
				// parameter to get the array-element type
				if (cls_t.getParameters() != null && cls_t.getParameters().size() > 0) {
					SVDBFindNamedModIfcClassIfc finder_c = 
						new SVDBFindNamedModIfcClassIfc(index_it);
					List<SVDBModIfcClassDecl> result =
						finder_c.find(cls_t.getParameters().get(0).getName());
					
					if (result.size() > 0) {
						cls_t = result.get(0);
						item_list.add(cls_t);
					}
				} else {
					System.out.println("Class " + cls_t.getName() + " doesn't have parameters");
				}
			}
		}
		
		return 0;
	}
	
	private int processPreTriggerId(
			ISVDBScopeItem		context,
			ITextScanner		scanner,
			String				id,
			String				preceeding_activator,
			boolean				resolveFinalReturnType,
			ISVDBIndexIterator	index_it,
			List<SVDBItem>		item_list) {
		// Read an identifier
		int ch = scanner.get_ch();
		
		debug("--> processPreTriggerId: id=" + id + " preceeding_activator=" + preceeding_activator);
		
		if (id == null) {
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		if (ch == '(' || ch == '\'') {
			String type_name = null;
			
			if (ch == '(') {
				// lookup id as a function
				debug("Look for function \"" + id + "\"");

				// TODO: must use scoped lookup by whatever preceeded
				SVDBItem search_ctxt = null;
				SVDBItem func = null;

				// If we have a previous lookup match earlier in the completion
				// string, then we should use that information to lookup this 
				// portion
				
				search_ctxt = (item_list.size() == 0)?null:item_list.get(item_list.size()-1);
				func = findTaskFunc(index_it, context, 
						search_ctxt, id, preceeding_activator);
				
				if (func == null) {
					return -1;
				}
				
				item_list.add(func);
				
				// Now, compute the return type of this function
				debug("return type is: " + ((SVDBTaskFuncScope)func).getReturnType());
				type_name = ((SVDBTaskFuncScope)func).getReturnType().getName(); 
			} else { // ch == '
				// ' indicates this is a type name
				type_name = id;
			}

			// Skip '()'
			// In both the case of a function/task call or a cast, 
			// we can ignore what's in the parens
			ch = scanner.skipPastMatch("()");


			// Only resolve this function return type of
			// it's not the last element in the string or
			// we want the type resolved
			if (ch != -1 || resolveFinalReturnType) {
				SVDBFindByName finder_name = 
					new SVDBFindByName(index_it, fDefaultMatcher);
				
				List<ISVDBItemBase> result = finder_name.find(type_name,
						SVDBItemType.Struct, SVDBItemType.Class);

				if (result.size() > 0) {
					item_list.add((SVDBItem)result.get(0));

					if (result.size() > 1) {
						System.out.println("[WARN] Lookup of \"" + type_name
								+ "\" resulted in " + result.size()
								+ " matches");
					}
				} else {
					// No point in continuing. We've failed to find a
					// match
					return -1;
				}
			}
		} else {
			// Unget 'ch', since we don't need it
			scanner.unget_ch(ch);
			
			SVDBItem field = null;
			List<ISVDBItemBase> matches = null;
			
			if (item_list.size() == 0) {
				// First element, so we need to lookup the item
				debug("Searching up scope for id=\"" + id + "\"");
				
				if (id.equals("this") || id.equals("super")) {
					SVDBModIfcClassDecl class_type = 
						SVDBSearchUtils.findClassScope(context);
					
					if (class_type != null) {
						matches = new ArrayList<ISVDBItemBase>();
					
						if (id.equals("this")) {
							matches.add(class_type);
						} else {
							SVDBFindSuperClass super_finder =
								new SVDBFindSuperClass(index_it);
							
							class_type = super_finder.find(class_type);
							
							if (class_type != null) {
								matches.add(class_type);
							}
						}
					}
				} else {
					if (context == null) {
						// With a null context, we're looking for classes, typedefs, and packages
						SVDBFindByName finder = new SVDBFindByName(index_it);
						
						matches = finder.find(id, SVDBItemType.Class, 
								SVDBItemType.Struct, SVDBItemType.PackageDecl,
								SVDBItemType.Typedef);
					} else {
						SVDBFindVarsByNameInScopes finder =
							new SVDBFindVarsByNameInScopes(index_it, fDefaultMatcher);
						
						matches = finder.find(context, id, true);
						
						fLog.debug("FindVarsByNameInScope \"" + id + "\" in scope \"" + 
								((ISVDBNamedItem)context).getName() + "\" returns " + matches.size() + " matches");
						
						if (matches != null && matches.size() > 0 && 
								matches.get(0) instanceof SVDBVarDeclItem) {
							SVDBItem cls_t = findVarType(
									index_it, (SVDBVarDeclItem)matches.get(0));
							if (cls_t != null) {
								matches.set(0, cls_t);
							}
						} else {
							// If this is the first element and we didn't find a field,
							// then this might be a static reference. Look for a type...
							if (preceeding_activator == null) {
								SVDBFindNamedModIfcClassIfc finder_c = 
									new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
								
								List<SVDBModIfcClassDecl> cls_l = finder_c.find(id);
								
								if (cls_l.size() > 0) {
									fLog.debug("Found \"" + id + "\" as a type");
									matches = new ArrayList<ISVDBItemBase>();
									matches.add(cls_l.get(0));
								} else {
									fLog.debug("Did not find \"" + id + "\" as a type");
								}
								/*
								SVDBModIfcClassDecl class_type = 
									SVDBSearchUtils.findClassScope(context);

								if (class_type != null) {
									SVDBFindByNameInClassHierarchy finder_c = 
										new SVDBFindByNameInClassHierarchy(index_it);
									matches = finder_c.find((SVDBScopeItem)class_type, id);
								}
								 */
							}
						}
					}
				}
			} else {
				// Lookup what follows based on the trigger
				SVDBItem search_ctxt = item_list.get(
						item_list.size()-1);

				debug("Searching type \"" + 
						search_ctxt.getName() + "\" for id=\"" + id + "\"");
				SVDBFindByNameInClassHierarchy finder = 
					new SVDBFindByNameInClassHierarchy(index_it, fDefaultMatcher);
				matches = finder.find((SVDBScopeItem)search_ctxt, id);
			}
			
//			debug("    result is " + matches.size() + " elements");
			
			if (matches == null || matches.size() == 0) {
				return -1;
			}
			
			field = (SVDBItem)matches.get(0);
			item_list.add(field);
			
			SVDBItem type = null;

			debug("field=" + field);
			if (field instanceof SVDBModIfcClassDecl ||
					field instanceof SVDBPackageDecl) {
				type = field;
			} else if (field instanceof SVDBVarDeclItem) {
				type = findVarType(index_it, (SVDBVarDeclItem)field);
			} else if (field instanceof SVDBTypedef) {
				SVDBTypedef td = (SVDBTypedef)field;
				if (td.getTypeInfo().getDataType() == SVDBDataType.Struct) {
					type = td.getTypeInfo();
				} else if (td.getTypeInfo().getDataType() == SVDBDataType.UserDefined) {
					SVDBFindNamedModIfcClassIfc finder = 
						new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
					debug("field is a user-defined type=\"" + td.getName() + "\" typeName=\"" + td.getTypeInfo().getName() + "\"");

					List<SVDBModIfcClassDecl> cl_l = finder.find(td.getName());
					type = (cl_l.size() > 0)?cl_l.get(0):null;
				}
			} else {
				fLog.error("Unknown scope type for \"" +
						field.getName() + "\" " + field.getClass().getName());
				return -1;
			}
					
			
			if (type == null) {
				fLog.error("cannot find type \"" + 
						((SVDBVarDeclItem)field).getTypeName() + "\"");
				return -1;
			}
			
			// TODO: lookup type of field
			debug("Adding type \"" + type.getName() + "\" to proposal list");
			item_list.add(type);
		}
		
		return 0;
	}
	
	private SVDBItem findVarType(
			ISVDBIndexIterator 	index_it,
			SVDBVarDeclItem 	field) {
		SVDBItem type = null;
		SVDBFindNamedModIfcClassIfc finder = 
			new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
		
		debug("findVarType: field=" + field.getName());
		
		// Determine pre-operations to resolve actual target type
		if (field.getTypeInfo().getDataType() == SVDBDataType.Struct) {
			type = field.getTypeInfo();
			debug("    field is of type struct");
		} else {
			String typename;
			List<SVDBModIfcClassDecl> cl_l = null;
			if (field instanceof SVDBParamPort) {
				typename = ((SVDBParamPort)field).getTypeName();
			} else {
				typename = ((SVDBVarDeclItem)field).getTypeName();
			}
			
			type = resolveClassType(index_it, typename);
			
			debug("    result of resolveClassType(" + typename + ") =>" + type);

			// Didn't find anything. Look at parameters in the class
			if (type == null) {
				cl_l = finder.find(typename);
				
				if (cl_l.size() == 0) {
					ISVDBChildItem field_p = field.getParent();
					while (field_p != null && field_p.getType() != SVDBItemType.Class) {
						field_p = field_p.getParent();
					}

					if (field_p != null) {
						SVDBModIfcClassDecl c_decl = (SVDBModIfcClassDecl)field_p;
						for (SVDBModIfcClassParam p : c_decl.getParameters()) {

							if (p.getName().equals(typename)) {
								cl_l = finder.find(p.getDefault());										
							}
						}
					}

					type = (cl_l.size() > 0)?cl_l.get(0):null;
				}
			}
		}
		
		// Now, handle special array and queue special cases
		int attr = field.getAttr();
		SVDBTypeInfo var_type = field.getTypeInfo();
		// The method for obtaining the name may change
		String var_type_name = var_type.getName();
		
		if ((attr & SVDBVarDeclItem.VarAttr_Queue) != 0 ||
			(attr & SVDBVarDeclItem.VarAttr_DynamicArray) != 0) {
			String base;
			if ((attr & SVDBVarDeclItem.VarAttr_Queue) != 0) {
				base = "__sv_builtin_queue";
			} else {
				base = "__sv_builtin_array";
			}
			SVDBParamValueAssignList params = 
				new SVDBParamValueAssignList();
			params.addParameter(
					new SVDBParamValueAssign("", var_type_name));
			SVDBTypeInfoUserDef type_info = new SVDBTypeInfoUserDef(
					base, SVDBDataType.UserDefined);
			type_info.setParameters(params);
			SVDBModIfcClassDecl cls_t = fParamClassFinder.find(type_info);
			
			if (cls_t != null) {
				type = cls_t;
			}
		} else if ((attr & SVDBVarDeclItem.VarAttr_AssocArray) != 0) {
			String base = "__sv_builtin_assoc_array";
			SVDBParamValueAssignList params = 
				new SVDBParamValueAssignList();
			params.addParameter(
					new SVDBParamValueAssign("", var_type_name));
			params.addParameter(
					new SVDBParamValueAssign("", field.getArrayDim()));
					
			SVDBTypeInfoUserDef type_info = 
				new SVDBTypeInfoUserDef(base);
			type_info.setParameters(params);
			SVDBModIfcClassDecl cls_t = fParamClassFinder.find(type_info);
			
			if (cls_t != null) {
				type = cls_t;
			}
		} else if (var_type.getDataType() == SVDBDataType.UserDefined &&
				((SVDBTypeInfoUserDef)var_type).getParameters() != null) {
			SVDBModIfcClassDecl cls_t = fParamClassFinder.find(
					(SVDBTypeInfoUserDef)var_type);
			
			if (cls_t != null) {
				type = cls_t;
			}
		} 

		return type;
	}
	
	private SVDBItem resolveClassType(
			ISVDBIndexIterator index_it, String typename) {
		SVDBItem type = null;
		SVDBFindNamedModIfcClassIfc finder = 
			new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
		
		List<SVDBModIfcClassDecl> cl_l = finder.find(typename);
		type = (cl_l.size() > 0)?cl_l.get(0):null;

		debug("Searching for class \"" + typename + "\" -- " + cl_l.size());

		// Didn't find anything. Try treating this as a typedef
		if (cl_l.size() == 0) {
			SVDBFindByName finder_n = new SVDBFindByName(index_it);

			List<ISVDBItemBase> result = finder_n.find(typename, SVDBItemType.Typedef);
			debug("Searching for typedef \"" + typename + "\" -- " + result.size());
			
			if (result.size() > 0) {
				SVDBTypedef td = (SVDBTypedef)result.get(0);
				debug("    typedef DataType=" + td.getTypeInfo().getDataType());
				if (td.getTypeInfo().getDataType() == SVDBDataType.Enum) {
					cl_l = finder.find(td.getTypeInfo().getName());
					type = (cl_l.size() > 0)?cl_l.get(0):null;
				} else if (td.getTypeInfo().getDataType() == SVDBDataType.Struct) {
					type = td.getTypeInfo();
				} else { // user-defined type
					cl_l = finder.find(td.getTypeInfo().getName());
					type = (cl_l.size() > 0)?cl_l.get(0):null;
				}
			} else {
				type = null;
			}
		}

		return type;
	}

	/*
	private SVDBModIfcClassDecl findVarType_2(SVDBItem item) {
		SVDBModIfcClassDecl ret = null;
		debug("--> findVarType: " + item.getType() + " " + item.getName());
		
		if (item instanceof SVDBVarDeclItem) {
			SVDBVarDeclItem var_decl = (SVDBVarDeclItem)item;
			int attr = var_decl.getAttr();
			SVDBTypeInfo var_type = var_decl.getTypeInfo();
			
			debug("    VarDeclItem: attr=0x" + Integer.toHexString(attr));
			
			// TODO: This seems to be the problem with array content assist
			// We search for
			if ((attr & SVDBVarDeclItem.VarAttr_Queue) != 0 ||
				(attr & SVDBVarDeclItem.VarAttr_DynamicArray) != 0) {
				String base;
				if ((attr & SVDBVarDeclItem.VarAttr_Queue) != 0) {
					base = "__sv_builtin_queue";
				} else {
					base = "__sv_builtin_array";
				}
				SVDBParamValueAssignList params = 
					new SVDBParamValueAssignList();
				params.addParameter(
						new SVDBParamValueAssign("", var_type.getName()));
				SVDBTypeInfoUserDef type_info = new SVDBTypeInfoUserDef(
						base, SVDBDataType.UserDefined);
				type_info.setParameters(params);
				SVDBModIfcClassDecl cls_t = fParamClassFinder.find(type_info);
				
				if (cls_t != null) {
					ret = cls_t;
				}
			} else if ((attr & SVDBVarDeclItem.VarAttr_AssocArray) != 0) {
				String base = "__sv_builtin_assoc_array";
				SVDBParamValueAssignList params = 
					new SVDBParamValueAssignList();
				params.addParameter(
						new SVDBParamValueAssign("", var_type.getName()));
				params.addParameter(
						new SVDBParamValueAssign("", var_decl.getArrayDim()));
						
				SVDBTypeInfoUserDef type_info = 
					new SVDBTypeInfoUserDef(base);
				type_info.setParameters(params);
				SVDBModIfcClassDecl cls_t = fParamClassFinder.find(type_info);
				
				if (cls_t != null) {
					ret = cls_t;
				}
			} else if (var_type.getDataType() == SVDBDataType.UserDefined &&
					((SVDBTypeInfoUserDef)var_type).getParameters() != null) {
				SVDBModIfcClassDecl cls_t = fParamClassFinder.find(
						(SVDBTypeInfoUserDef)var_type);
				
				if (cls_t != null) {
					ret = cls_t;
				}
			} 
		} else if (item.getType() == SVDBItemType.Typedef) {
			SVDBFindNamedModIfcClassIfc finder_c = 
				new SVDBFindNamedModIfcClassIfc(fIndexIt, fDefaultMatcher);
			SVDBTypedef td = (SVDBTypedef)item;
			
			if (td.getTypeInfo().getDataType() == SVDBDataType.UserDefined) {
				SVDBTypeInfoUserDef type = (SVDBTypeInfoUserDef)td.getTypeInfo();
				fLog.debug("Lookup typename \"" + type.getName() + "\"");
				
				List<SVDBModIfcClassDecl> cls_l = finder_c.find(type.getName());
				
				if (cls_l.size() > 0) {
					ret = cls_l.get(0);
				}
				
			} else {
				fLog.debug("Not looking up typename \"" + td.getTypeInfo().getDataType() + "\"");
			}
			
		}
		
		debug("<-- findVarType: " + item.getType() + " " + item.getName() + " " + ret);
		return ret;
	}
	 */
	
	private SVDBTaskFuncScope findTaskFunc(
			ISVDBIndexIterator		index_it,
			ISVDBScopeItem			context,
			SVDBItem 				search_ctxt,
			String					id,
			String					preceeding_activator) {
		SVDBTaskFuncScope func = null;
		
		if (search_ctxt == null) {
			SVDBFindByNameInScopes finder_scopes =
				new SVDBFindByNameInScopes(index_it);
			
			List<SVDBItem> matches = finder_scopes.find(
					context, id, true,
					SVDBItemType.Function, SVDBItemType.Task);

			debug("first-item search for \"" + id + 
					"\" returned " + matches.size() + " matches");
			
			if (matches.size() > 0) {
				func = (SVDBTaskFuncScope)matches.get(0);
			}
		} else {
			SVDBFindByNameInClassHierarchy finder_h =
				new SVDBFindByNameInClassHierarchy(index_it, fDefaultMatcher);
			
			List<ISVDBItemBase> matches = finder_h.find((SVDBScopeItem)search_ctxt, 
					id, SVDBItemType.Function);
				
			debug("next-item search for \"" + id + 
					"\" in \"" + search_ctxt.getName() + 
					"\" returned " + matches.size() + " matches");
			
			func = (SVDBTaskFuncScope)filterByAttr(matches, preceeding_activator);
		}
		
		return func;
	}
	
	private SVDBItem filterByAttr(List<ISVDBItemBase> items, String trigger) {
		SVDBItem ret = null;
		
		for (ISVDBItemBase it : items) {
			int attr = 0;
			
			if (it.getType() == SVDBItemType.Task || it.getType() == SVDBItemType.Function) {
				attr = ((SVDBTaskFuncScope)it).getAttr();
			} else if (it.getType() == SVDBItemType.VarDecl) {
				attr = ((SVDBVarDeclItem)it).getAttr();
			}
			
			if (trigger != null && trigger.equals("::")) {
				if ((attr & IFieldItemAttr.FieldAttr_Static) != 0) {
					ret = (SVDBItem)it;
					break;
				}
			} else {
				ret = (SVDBItem)it;
				break;
			}
		}
		
		return ret;
	}

	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}
