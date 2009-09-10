package net.sf.sveditor.core.expr_utils;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindByName;
import net.sf.sveditor.core.db.search.SVDBFindByNameInClassHierarchy;
import net.sf.sveditor.core.db.search.SVDBFindByNameInScopes;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.search.SVDBFindSuperClass;
import net.sf.sveditor.core.db.search.SVDBFindVarsByNameInScopes;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class SVExpressionUtils {
	
	private boolean fDebugEn = false;
	
	
	/**
	 * Extracts an expression surrounding the current scan position.
	 * 
	 * @param scanner
	 * @param leaf_scan_fwd	- Scan forward from the start point for Leaf. 
	 * @return
	 */
	public SVExprContext extractExprContext(
			IBIDITextScanner 		scanner,
			boolean					leaf_scan_fwd) {
		SVExprContext ret = new SVExprContext();
		debug("--> extractExprContext()");

		int c = -1, last_c = -1;

		long offset = scanner.getPos();
		
		// Scan forward (adjust offset) until 
		if (leaf_scan_fwd) {
			scanner.setScanFwd(true);
			
			while (((c = scanner.get_ch()) != -1) && 
					Character.isJavaIdentifierPart(c)) {}
			offset = scanner.getPos();
		}

		long start;
		scanner.setScanFwd(false);

		// Scan backwards to an activation character or the beginning of
		// line
		debug("-- scan back to activation character");
		while ((c = scanner.get_ch()) != -1) {
			if (c == '.' || c == '`' ||	
					(c == ':' && last_c == ':')	|| c == '\n' ||
					c == ',' || c == '(') {
				debug("  ** stop -- saw activator character");
				break;
			} else if (c == ')') {
				// scan back to matching
				int matchLevel = 1;
				while ((c = scanner.get_ch()) != -1) {
					if (c == '(') {
						matchLevel--;
					} else if (c == ')') {
						matchLevel++;
					}
				}
			}
			last_c = c;
		}
		start = scanner.getPos()+1;
		
		debug("-- done scanning back to activator char \"" + (char)c + "\"");
		debug("    start=" + start);

		if (c == '.' || c == '`') {
			ret.fTrigger = "" + (char) c;
		} else if (c == ':' && last_c == ':') {
			ret.fTrigger = "::";
		} else if (c == '\n') {
			// Scan forward so 'start' actually points at the beginning of the
			// token
			ret.fTrigger = "";
			
			scanner.setScanFwd(true);
			while ((c = scanner.get_ch()) != -1 && Character.isWhitespace(c)) {}
			start = scanner.getPos()-1;
		} else {
			ret.fTrigger = "";
		}
		
		if (!ret.fTrigger.equals("")) {
			// There is a trigger, so use that as a reference point
			ret.fLeaf = scanner.get_str(start, (int)(offset-start)).trim();
			ret.fRoot = extractPreTriggerPortion(scanner);
		} else {
			ret.fLeaf = scanner.get_str(start, (int)(offset-start)).trim();

			/*
			if (c == '(' || c == ',' || c == '>' || c == '<') {
				ret.fStart = (int)scanner.getPos()+1;
				scanner.setScanFwd(true);
				scanner.seek(ret.fStart);

				// Scan forward to avoid any whitespace
				while ((c = scanner.get_ch()) != -1 && ret.fStart < offset &&  
						Character.isWhitespace(c)) {
					ret.fStart++;
				}
				ret.fPre = scanner.get_str(ret.fStart, (int)scanner.getPos());
			} else {
				// No recognizable trigger character, so set 'pre' based on
				// seeking backwards from the offset passed in
				// idx = offset - 1;
				scanner.seek(offset-1);
				scanner.setScanFwd(false);

				// Only works in certain cases...
				while ((c = scanner.get_ch()) != -1
						&& !Character.isWhitespace(c)) {}

				ret.fStart = (int)scanner.getPos()+1;
				
				System.out.println("offset=" + offset + " start=" + ret.fStart);
				if (offset > ret.fStart) {
					ret.fPre = scanner.get_str(
							ret.fStart, (int)(offset-ret.fStart-1)).trim();
					System.out.println("pre=" + ret.fPre);
				} else {
					// TODO: not quite sure how to handle this
					System.out.println("offset < start");
					return null;
				}
			}
			 */
		}

		ret.fStart = (int)start;

		debug("<-- extractExprContext()");
		
		return ret;
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
		String end_match[] = { "nde", // end
				"nigeb", // begin
				";",
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
			// TODO: idx--;

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
	public List<SVDBItem> processPreTriggerPortion(
			ISVDBIndexIterator			index_it,
			SVDBScopeItem				context,
			String						preTrigger,
			boolean						allowNonClassLastElem) {
		List<SVDBItem> item_list = new ArrayList<SVDBItem>();
		
		int ret = processPreTriggerPortion(0, null, item_list, 
				index_it, context, preTrigger, allowNonClassLastElem);
		
		if (ret == -1) {
			return null;
		} else {
			return item_list;
		}
	}

	/**
	 * Process the pre-trigger portion of a context string
	 * 
	 * @param searcher
	 * @param context
	 * @param preTrigger
	 * @return
	 */
	public List<SVDBItem> processPreTriggerPortion_2(
			ISVDBIndexIterator			index_it,
			SVDBScopeItem				context,
			String						preTrigger,
			boolean						allowNonClassLastElem) {
		List<SVExprItemInfo> info_list = new ArrayList<SVExprItemInfo>();
		
		if (processPreTriggerPortion(0, null, info_list, preTrigger) == -1) {
			return null;
		}
		
		List<SVDBItem> item_list = new ArrayList<SVDBItem>();
		
		for (SVExprItemInfo info : info_list) {
			switch (info.getType()) {
				case TaskFunc:
					break;
					
				case SubExpr:
					break;
					
				case Id:
					break;
			}
		}

		return item_list;
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
			int							idx,
			String						preceeding_activator,
			List<SVDBItem>				item_list,
			ISVDBIndexIterator			index_it,
			SVDBScopeItem				context,
			String						preTrigger,
			boolean						resolveFinalReturnType) {
		String id = null;
		
		debug("processPreTriggerPortion(idx=" + idx + " preceeding_activator=" + preceeding_activator);
		// Need to make some changes to track the preceeding character, not the
		// next. For example, if the preceeding character was '.', then we should
		// look for id() within typeof(ret.item)
		while (idx < preTrigger.length()) {
			int ch = preTrigger.charAt(idx);
			idx++;

			if (ch == '(') {
				// recursively expand
				idx = processPreTriggerPortion(
						idx, preceeding_activator, item_list,
						index_it, context, preTrigger, resolveFinalReturnType);
				
				// Give up because the lower-level parser did...
				if (idx == -1) {
					break;
				}
			} else if (ch == '.') {
				// use the preceeding
				preceeding_activator = ".";
			} else if (ch == ':' && 
					idx < preTrigger.length() && 
					preTrigger.charAt(idx) == ':') {
				idx++;
				preceeding_activator = "::";
			} else if (Character.isJavaIdentifierPart(ch)) {
				// Read an identifier
				StringBuffer tmp = new StringBuffer();

				tmp.append((char) ch);
				while (idx < preTrigger.length()
						&& Character.isJavaIdentifierPart(
								(ch = preTrigger.charAt(idx)))) {
					tmp.append((char) ch);
					idx++;
				}
				id = tmp.toString();
				
				debug("id=" + id + " ch after id=" + (char)ch);

				if (ch == '(' || ch == '\'') {
					String type_name = null;
					int elem_type = ch;
					
					if (ch == '(') {
						// lookup id as a function
						debug("Look for function \"" + id + "\"");

						// TODO: must use scoped lookup by whatever preceeded
						List<SVDBItem> matches = null;
						SVDBItem search_ctxt = null;
						SVDBItem func = null;

						// If we have a previous lookup match earlier in the completion
						// string, then we should use that information to lookup this 
						// portion
						
						if (item_list.size() == 0) {
							// This is the first item.
							// - Search the class/module parent of the active scope

							// Browse up the search context to reach the class scope
							// TODO: Also want to support package-scope items (?)
							
							SVDBFindByNameInScopes finder_scopes =
								new SVDBFindByNameInScopes(index_it);
							
							matches = finder_scopes.find(context, id, true);

							debug("first-item search for \"" + id + 
									"\" returned " + matches.size() + " matches");
							
							if (matches.size() > 0) {
								func = matches.get(0);
							}
						} else {
							search_ctxt = item_list.get(item_list.size()-1);
							
							SVDBFindByNameInClassHierarchy finder_h =
								new SVDBFindByNameInClassHierarchy(index_it);
							
							
							matches = finder_h.find((SVDBScopeItem)search_ctxt, id,
									SVDBItemType.Function);
								
							debug("next-item search for \"" + id + 
									"\" in \"" + search_ctxt.getName() + 
									"\" returned " + matches.size() + " matches");
							
							if (matches.size() > 0) {
								func = matches.get(0);
							}
						}
						
						if (func == null) {
							return -1;
						}
						
						item_list.add(func);
						
						// Now, compute the return type of this function
						debug("return type is: " + ((SVDBTaskFuncScope)func).getReturnType());
						type_name = ((SVDBTaskFuncScope)func).getReturnType(); 
					} else {
						// ' indicates this is a type name
						// TODO: We don't yet have the infrastructure to deal with types
						type_name = id;
						SVDBFindByName finder_name = new SVDBFindByName(index_it);
						
						List<SVDBItem> result = finder_name.find(id,
								SVDBItemType.Class, SVDBItemType.Struct);
					}

					// Skip '()'
					// In both the case of a function/task call or a cast, 
					// we can ignore what's in the parens
					int matchLevel = 1;

					debug("pre-skip =" + (char)preTrigger.charAt(idx));
					while (matchLevel > 0 && ++idx < preTrigger.length()) {
						ch = preTrigger.charAt(idx);
						if (ch == '(') {
							matchLevel++;
						} else if (ch == ')') {
							matchLevel--;
						}
					}
					idx++;

					/*
					if (idx < preTrigger.length()) {
						System.out.println("post-consume () - idx=" + idx + 
								" len=" + preTrigger.length() + "(" + 
								preTrigger.charAt(idx) + ")");
					} else {
						System.out.println("post-consume () - exceeded length");
					}
					 */

					// Only resolve this function return type of
					// it's not the last element in the string or
					// we want the type resolved
					if (idx < preTrigger.length() || resolveFinalReturnType) {
						SVDBFindByName finder_name = new SVDBFindByName(index_it);
						
						List<SVDBItem> result = finder_name.find(type_name, 
								SVDBItemType.Struct, SVDBItemType.Class);

						if (result.size() > 0) {
							item_list.add(result.get(0));

							if (result.size() > 1) {
								System.out.println("[WARN] Lookup of \"" + type_name
										+ "\" resulted in " + result.size()
										+ " matches");
							}
						} else {
							idx = -1;

							// No point in continuing. We've failed to find a
							// match
							break;
						}
					}
				} else {
					// 
					SVDBItem field = null;
					List<SVDBItem> matches = null;
					
					if (item_list.size() == 0) {
						// First element, so we need to lookup the item
						debug("Searching up scope for id=\"" + id + "\"");
						
						if (id.equals("this") || id.equals("super")) {
							SVDBModIfcClassDecl class_type = 
								SVDBSearchUtils.findClassScope(context);
							
							if (class_type != null) {
								matches = new ArrayList<SVDBItem>();
							
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
							SVDBFindVarsByNameInScopes finder =
								new SVDBFindVarsByNameInScopes(index_it);
							
							matches = finder.find(context, id, true);
							
							debug("matches.size=" + matches.size());

							if (matches == null || matches.size() == 0) {
								SVDBModIfcClassDecl class_type = 
									SVDBSearchUtils.findClassScope(context);

								if (class_type != null) {
									SVDBFindByNameInClassHierarchy finder_c = 
										new SVDBFindByNameInClassHierarchy(index_it);
									matches = finder_c.find((SVDBScopeItem)class_type, id);
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
							new SVDBFindByNameInClassHierarchy(index_it);
						matches = finder.find((SVDBScopeItem)search_ctxt, id);
					}
					
//					debug("    result is " + matches.size() + " elements");
					
					if (matches == null || matches.size() == 0) {
						return -1;
					}
					
					field = matches.get(0);
					item_list.add(field);
					
					SVDBItem type = null;

					debug("field=" + field);
					if (field instanceof SVDBModIfcClassDecl) {
						type = field;
					} else {
						SVDBFindNamedModIfcClassIfc finder = 
							new SVDBFindNamedModIfcClassIfc(index_it);
						type = finder.find(((SVDBVarDeclItem)field).getTypeName());
					}
							
					
					if (type == null) {
						System.out.println("cannot find type \"" + 
								((SVDBVarDeclItem)field).getTypeName() + "\"");
						return -1;
					}
					
					// TODO: lookup type of field
					debug("Adding type \"" + type.getName() + "\" to proposal list");
					item_list.add(type);
				}
			} else {
				// TODO: This is actually an error (?)
				System.out.println("CHECK: ch=" + (char)ch + " is this an error?");
				return -1;
			}
		}

		return idx;
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
	 * @return
	 */
	public int processPreTriggerPortion(
			int							idx,
			String						preceeding_activator,
			List<SVExprItemInfo>		item_list,
			String						preTrigger) {
		String id = null;
		
		debug("processPreTriggerPortion(idx=" + idx + " preceeding_activator=" + preceeding_activator);
		// Need to make some changes to track the preceeding character, not the
		// next. For example, if the preceeding character was '.', then we should
		// look for id() within typeof(ret.item)
		while (idx < preTrigger.length()) {
			int ch = preTrigger.charAt(idx);
			idx++;

			if (ch == '(') {
				// recursively expand
				idx = processPreTriggerPortion(
						idx, preceeding_activator, item_list, preTrigger);
				
				// Give up because the lower-level parser did...
				if (idx == -1) {
					break;
				}
			} else if (ch == '.') {
				// use the preceeding
				preceeding_activator = ".";
			} else if (ch == ':' && 
					idx < preTrigger.length() && 
					preTrigger.charAt(idx) == ':') {
				idx++;
				preceeding_activator = "::";
			} else if (Character.isJavaIdentifierPart(ch)) {
				// Read an identifier
				StringBuffer tmp = new StringBuffer();

				tmp.append((char) ch);
				while (idx < preTrigger.length()
						&& Character.isJavaIdentifierPart(
								(ch = preTrigger.charAt(idx)))) {
					tmp.append((char) ch);
					idx++;
				}
				id = tmp.toString();
				
				debug("id=" + id + " ch after id=" + (char)ch);

				if (ch == '(' || ch == '\'') {
					String type_name = null;
					int elem_type = ch;
					
					if (ch == '(') {
						// lookup id as a function
						debug("Look for function \"" + id + "\"");

						item_list.add(
								new SVExprItemInfo(SVExprItemType.TaskFunc, id));
					} else {
						// ' indicates this is a type name
						// TODO: We don't yet have the infrastructure to deal with types
						item_list.add(
								new SVExprItemInfo(SVExprItemType.TypeId, id));
					}

					// Skip '()'
					// In both the case of a function/task call or a cast, 
					// we can ignore what's in the parens
					int matchLevel = 1;

					debug("pre-skip =" + (char)preTrigger.charAt(idx));
					while (matchLevel > 0 && ++idx < preTrigger.length()) {
						ch = preTrigger.charAt(idx);
						if (ch == '(') {
							matchLevel++;
						} else if (ch == ')') {
							matchLevel--;
						}
					}
					idx++;
				} else { // not ' and not (
					item_list.add(new SVExprItemInfo(SVExprItemType.Id, id));
				}
			} else {
				// TODO: This is actually an error (?)
				System.out.println("CHECK: ch=" + (char)ch + " is this an error?");
				return -1;
			}
		}

		return idx;
	}

	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
