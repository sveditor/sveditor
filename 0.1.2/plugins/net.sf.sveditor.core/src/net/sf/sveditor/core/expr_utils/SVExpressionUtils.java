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

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
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
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

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
	
	public SVExpressionUtils(ISVDBFindNameMatcher matcher) {
		fLog = LogFactory.getLogHandle("SVExpressionUtils");
		fNameMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
	}
	
	public void setMatcher(ISVDBFindNameMatcher matcher) {
		fNameMatcher = matcher;
	}
	
	
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

		int c = -1;
		
		boolean scan_fwd = scanner.getScanFwd();
		scanner.setScanFwd(false);
		debug("    First Ch (non-adjusted): \"" + (char)scanner.get_ch() + "\"");
		scanner.unget_ch(-1);
		scanner.setScanFwd(scan_fwd);

		// We'll start by scanning backwards. On entry, the
		// cursor has been placed to read going forward
		if (scanner.getScanFwd() && scanner.getPos() > 0) {
			debug("Adjust position: old=\"" + scanner.get_str(scanner.getPos(), 1) + "\" new=\"" +
					scanner.get_str(scanner.getPos()-1, 1) + "\"");
			scanner.seek(scanner.getPos()-1);
		}
		
		scanner.setScanFwd(false);
		
		debug("    First Ch (adjusted): \"" + (char)scanner.get_ch() + "\"");
		scanner.unget_ch(-1);

		// Check whether we're currently in a string
		if (isInString(scanner)) {
			debug("isInString()");
			// It's most likely that we're looking at an include

			ret.fLeaf = readString(scanner, leaf_scan_fwd);
			
			long seek = scanner.getPos();
			scanner.setScanFwd(true);
			while ((c = scanner.get_ch()) != -1 && c != '"') {
			}
			
			if (c == '"') {
				ret.fStart = (int)scanner.getPos();
			} else {
				ret.fStart = (int)seek;
			}
			scanner.seek(seek);
			
			if (ret.fLeaf == null) {
				ret.fLeaf = "";
			}
			
			// Now, continue scanning backwards to determine how to
			// deal with this
			scanner.setScanFwd(false);
			c = scanner.skipWhite(scanner.get_ch());

			debug("string=\"" + ret.fLeaf + "\" next=\"" + (char)c + "\"");

			if (SVCharacter.isSVIdentifierPart(c)) {
				String id = new StringBuilder(scanner.readIdentifier(c)).reverse().toString();
				debug("id=\"" + id + "\"");
				
				c = scanner.skipWhite(scanner.get_ch());
				
				debug("next=\"" + (char)c + "\"");
				
				if (c == '`' && id.equals("include")) {
					ret.fTrigger = "`";
					ret.fRoot = "include";
				}
			}
		} else {
			if (SVCharacter.isSVIdentifierPart((c = scanner.get_ch()))) {
				debug("notInString c=\"" + (char)c + "\"");
				scanner.unget_ch(c);
				String id = readIdentifier(scanner, leaf_scan_fwd);
				ret.fStart = (int)scanner.getPos()+1; // compensate for begin in scan-backward mode
				ret.fLeaf = id;
				
				debug("id=\"" + id + "\"");

				// See if we're working with a triggered expression
				ret.fTrigger = readTriggerStr(scanner);
				debug("trigger=\"" + ret.fTrigger + "\"");
				
				if (ret.fTrigger != null && !ret.fTrigger.equals("`")) {
					// Read an expression
					ret.fRoot = readExpression(scanner);
				} else if (ret.fTrigger == null) {
						
					// Just process the identifier
					c = scanner.skipWhite(scanner.get_ch());
					
					if (SVCharacter.isSVIdentifierPart(c)) {
						ret.fRoot = scanner.readIdentifier(c);
					}
				}
			} else {
				// backup and try for a triggered identifier
				debug("notInId: ch=\"" + (char)c + "\"");
				
				scanner.unget_ch(c);
				
				ret.fStart = (int)scanner.getPos()+1; // compensate for begin in scan-backward mode
				
				if ((ret.fTrigger = readTriggerStr(scanner)) != null) {
					if (scan_fwd) {
						scanner.setScanFwd(true);
						c = scanner.get_ch();
						fLog.debug("post-trigger c=\"" + (char)c + "\"");
						ret.fLeaf = readIdentifier(scanner, true);
						
						// Now, back up to ensure that we get the pre-trigger portion
						scanner.setScanFwd(false);
						c = scanner.get_ch();
						fLog.debug("post-leaf c=\"" + (char)c + "\"");
					} else {
						ret.fLeaf = "";
					}
					ret.fRoot = readExpression(scanner);
				}
			}
		}
		
		debug("<-- extractExprContext()");
		
		if (ret.fRoot == null && ret.fTrigger == null && ret.fLeaf == null) {
			ret.fLeaf = "";
		}
		
		return ret;
	}
	
	public List<SVDBItem> findItems(
			ISVDBIndexIterator	index_it,
			SVDBScopeItem		active_scope,
			SVExprContext		expr_ctxt,
			boolean				match_prefix) {
		return findItems(index_it, active_scope, expr_ctxt, match_prefix, 0);
		
	}
	
	public List<SVDBItem> findItems(
			ISVDBIndexIterator	index_it,
			SVDBScopeItem		active_scope,
			SVExprContext		expr_ctxt,
			boolean				match_prefix,
			int					max_matches) {
		fLog.debug("--> findItems(active_scope=\"" + 
				((active_scope != null)?active_scope.getName():null) + "\" " +
				" root=\"" + expr_ctxt.fRoot + "\" trigger=\"" + expr_ctxt.fTrigger +
				"\" leaf=\"" + expr_ctxt.fLeaf + "\" match_prefix=" + match_prefix + ")");
		
		List<SVDBItem> ret = new ArrayList<SVDBItem>();

		StringBuffer text = new StringBuffer();

		if (expr_ctxt.fTrigger != null) {
			if (expr_ctxt.fTrigger.equals("`")) {
				if (expr_ctxt.fRoot != null && expr_ctxt.fRoot.equals("include")) {
					SVDBFindIncludedFile finder = new SVDBFindIncludedFile(
							index_it, fNameMatcher);
					List<SVDBFile> it_l = finder.find(expr_ctxt.fLeaf);

					if (it_l.size() > 0 && (max_matches == 0 || ret.size() < max_matches)) {
						ret.addAll(it_l);
					}
				} else {
					// most likely a macro call
					ISVDBItemIterator<SVDBItem> it_i = index_it.getItemIterator();
					while (it_i.hasNext()) {
						SVDBItem it_t = it_i.nextItem();

						if (it_t.getType() == SVDBItemType.Macro) {
							if (match_prefix) {
								if (expr_ctxt.fLeaf.equals("") || 
										it_t.getName().startsWith(expr_ctxt.fLeaf)) {
									if (max_matches == 0 || (ret.size() < max_matches)) {
										ret.add(it_t);
									} else {
										break;
									}
								}
							} else {
								if (it_t.getName().equals(expr_ctxt.fLeaf)) {
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
			} else {
				fLog.debug("Expression is triggered expression");
				List<SVDBItem> pre_trigger = processPreTriggerPortion(
						index_it, active_scope, expr_ctxt.fRoot, !match_prefix);
				
				if (pre_trigger != null && pre_trigger.size() != 0) {
					SVDBItem it_t = pre_trigger.get(pre_trigger.size()-1);
					
					fLog.debug("Using " + it_t.getType() + " " + 
							it_t.getName() + " as search base");

					if (it_t.getType() == SVDBItemType.Class || it_t.getType() == SVDBItemType.Struct) {
						SVDBFindByNameInClassHierarchy finder_h = 
							new SVDBFindByNameInClassHierarchy(index_it, fNameMatcher);
						List<SVDBItem> fields = finder_h.find(
								(SVDBScopeItem)it_t, expr_ctxt.fLeaf);
						
						fLog.debug("Find Named Field returns " + fields.size() + " results");
						for (SVDBItem it : fields) {
							fLog.debug("    " + it.getType() + " " + it.getName());
						}

						if (fields.size() > 0) {
							if (max_matches == 0 || (ret.size() < max_matches)) {
								ret.addAll(fields);
							}
						}
					} else {
						fLog.debug("Target type is " + it_t.getType() + " -- cannot search");
					}
				}
			}
		} else {		
			// No trigger info. Re-do this search by reading the identifier surrounding
			// the cursor location

			text.setLength(0);
			text.append(expr_ctxt.fLeaf);

			fLog.debug("Looking for un-triggered identifier \"" + 
					text.toString() + "\"");
			List<SVDBItem> result = null;
			
			SVDBFindByNameInClassHierarchy finder_h =
				new SVDBFindByNameInClassHierarchy(index_it, fNameMatcher);

			result = finder_h.find(active_scope, text.toString());

			if (result.size() > 0) {
				if (max_matches == 0 || (ret.size() < max_matches)) {
					ret.addAll(result);
				}
			}

			// Try type names
			SVDBFindNamedModIfcClassIfc finder_cls =
				new SVDBFindNamedModIfcClassIfc(index_it, fNameMatcher);

			List<SVDBModIfcClassDecl> cl_l = finder_cls.find(text.toString());
			
			if (cl_l.size() > 0) {
				fLog.debug("Global type search for \"" + text.toString() + 
						"\" returned " + cl_l.size());
				for (SVDBModIfcClassDecl cl : cl_l) {
					fLog.debug("    " + cl.getType() + " " + cl.getName());
				}
				if (max_matches == 0 || ret.size() < max_matches) {
					ret.addAll(cl_l);
				}
			} else {
				fLog.debug("Global class find for \"" + text.toString() + 
						"\" returned no results");
			}
		
			// Try global task/function
			SVDBFindByName finder_tf = new SVDBFindByName(index_it, fNameMatcher);
			
			List<SVDBItem> it_l= finder_tf.find(text.toString(),
					SVDBItemType.Task, SVDBItemType.Function, SVDBItemType.Typedef);
			
			if (it_l != null && it_l.size() > 0) {
				fLog.debug("Global find-by-name \"" + text.toString() + 
						"\" returned:");
				for (SVDBItem it : it_l) {
					fLog.debug("    " + it.getType() + " " + it.getName());
				}
				
				if (max_matches == 0 || (ret.size() < max_matches)) {
					ret.addAll(it_l);
				}
			} else {
				fLog.debug("Global find-by-name \"" + text.toString() + 
						"\" returned no results");
			}
		}

		fLog.debug("<-- findItems(root=\"" + expr_ctxt.fRoot + "\" trigger=\"" + 
				expr_ctxt.fTrigger + "\" leaf=\"" + expr_ctxt.fLeaf + 
				"\" match_prefix=" + match_prefix + ") returns " + ret.size() + " results");
		return ret;
	}
	
	/**
	 * Read a string surrounding the current position. The scanner will
	 * be left at the beginning of the string.
	 * 
	 * @param scanner
	 * @param scan_fwd
	 * @return
	 */
	private String readString(IBIDITextScanner scanner, boolean scan_fwd) {
		int ch;
		
		long end_pos = scanner.getPos();
		long start_pos = -1, seek;
		
		// First, scan back to the string beginning
		scanner.setScanFwd(false);
		while ((ch = scanner.get_ch()) != -1 && 
				ch != '\n' && ch != '"') {
			debug("readString: ch=\"" + (char)ch + "\"");
		}
		
		start_pos = scanner.getPos();
		
		if (ch == '"') {
			seek = start_pos-1;
			start_pos += 2;
		} else {
			seek = start_pos;
		}
		
		if (scan_fwd) {
			scanner.setScanFwd(true);
			scanner.seek(start_pos);
			
			while ((ch = scanner.get_ch()) != -1 &&
					ch != '"' && ch != '\n') { 
			}
			
			end_pos = (scanner.getPos()-1);
			if (ch == '"') {
				end_pos--;
			}
		}
		
		scanner.seek(seek);
		
		if (start_pos >= 0 && (end_pos-start_pos) > 0) {
			return scanner.get_str(start_pos, (int)(end_pos-start_pos+1));
		} else {
			return "";
		}
	}

	/**
	 * readIdentifier()
	 * 
	 * Reads the identifier surrounding the current location. 
	 * 
	 * @param scanner
	 * @param scan_fwd
	 * @return
	 */
	private String readIdentifier(IBIDITextScanner scanner, boolean scan_fwd) {
		int ch;
		fLog.debug("--> readIdentifier(scan_fwd=" + scan_fwd + ")");
		
		long end_pos = (scanner.getScanFwd())?scanner.getPos():(scanner.getPos()+1);
		long start_pos = -1, seek;
		
		// First, scan back to the string beginning
		scanner.setScanFwd(false);
		while ((ch = scanner.get_ch()) != -1 &&
				SVCharacter.isSVIdentifierPart(ch)) { }
		
		start_pos = scanner.getPos() + 2;
		seek = scanner.getPos() + 1;
		
		if (scan_fwd) {
			scanner.setScanFwd(true);
			scanner.seek(start_pos);
			
			while ((ch = scanner.get_ch()) != -1 &&
					SVCharacter.isSVIdentifierPart(ch)) { }
			
			end_pos = scanner.getPos() - 1;
		}
		
		scanner.seek(seek);

		fLog.debug("<-- readIdentifier(scan_fwd=" + scan_fwd + ")");
		return scanner.get_str(start_pos, (int)(end_pos-start_pos));
	}
	
	/**
	 * 
	 * @param scanner
	 * @return
	 */
	private String readTriggerStr(IBIDITextScanner scanner) {
		long start_pos = scanner.getPos();
		scanner.setScanFwd(false);
		int ch = scanner.skipWhite(scanner.get_ch());
		
		if (ch == '.' || ch == '`') {
			return "" + (char)ch;
		} else if (ch == ':') {
			int ch2 = scanner.get_ch();
			
			if (ch2 == ':') {
				return "::";
			}
		}
		
		// If we didn't identify a trigger, then restore the
		// previous position
		scanner.seek(start_pos);
		return null;
	}

	private boolean isInString(IBIDITextScanner scanner) {
		boolean ret = false;
		long sav_pos = scanner.getPos();
		boolean scan_fwd = scanner.getScanFwd();
		int ch;
		
		// Continue scanning backwards
		scanner.setScanFwd(false);
		while ((ch = scanner.get_ch()) != -1 && 
				ch != '"' && ch != '\n') {
		}
		
		if (ch == '"') {
			ret = true;
			
			// Just to be sure, continue scanning backwards to
			// be sure we don't find another matching quite
			while ((ch = scanner.get_ch()) != -1 &&
					ch != '"' && ch != '\n') { }
			
			if (ch == '"') {
				ret = false;
			}
		}
		
		scanner.seek(sav_pos);
		scanner.setScanFwd(scan_fwd);
		return ret;
	}
	
	private String readExpression(IBIDITextScanner scanner) {
		int ch;
		String trigger = null;
		
		fLog.debug("--> readExpression");
		// Continue moving backwards
		scanner.setScanFwd(false);
		
		ch = scanner.skipWhite(scanner.get_ch());
		scanner.unget_ch(ch);
		long end_pos = scanner.getPos(), start_pos;
		
		do {
			ch = scanner.skipWhite(scanner.get_ch());
			fLog.debug("    trigger=\"" + trigger + "\" ch=\"" + (char)ch + "\"");
			
			if (ch == ')') {
				scanner.skipPastMatch(")(");
			} else if (ch == ']') {
				// Skip what's in an array reference
				ch = scanner.skipPastMatch("][");
				if (SVCharacter.isSVIdentifierPart(ch)) {
					scanner.readIdentifier(ch);
				}
			} else if (SVCharacter.isSVIdentifierPart(ch)) {
				scanner.readIdentifier(ch);
			} else {
				fLog.error("unknown ch \"" + (char)ch + "\"");
			}
			start_pos = (scanner.getPos()+1);
		} while ((trigger = readTriggerStr(scanner)) != null);
		
		fLog.debug("<-- readExpression");
		
		return scanner.get_str(start_pos, (int)(end_pos-start_pos+1)).trim();
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
		SVDBFindParameterizedClass pclass_finder = new SVDBFindParameterizedClass(index_it);
		
		debug("--> processPreTriggerPortion(idx=" + idx + " preceeding_activator=" + preceeding_activator + ")");
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
			} else if (ch == '[') {
				// TODO: This is an array reference. Must find base type of preceeding variable
				int l_match = 1, r_match = 0;
				
				while (idx < preTrigger.length() && l_match != r_match) {
					ch = preTrigger.charAt(idx++);
					if (ch == '[') {
						l_match++;
					} else if (ch == ']') {
						r_match++;
					}
				}
				
				if (item_list.size() > 0 && 
						item_list.get(item_list.size()-1).getType() == SVDBItemType.Class) {
					SVDBModIfcClassDecl cls_t = (SVDBModIfcClassDecl)
						item_list.get(item_list.size()-1);
					
					if (cls_t.getParameters() != null) {
						SVDBFindNamedModIfcClassIfc finder_c = 
							new SVDBFindNamedModIfcClassIfc(index_it);						
						List<SVDBModIfcClassDecl> result =
							finder_c.find(cls_t.getParameters().get(0).getName());
						
						if (result.size() > 0) {
							cls_t = result.get(0);
							item_list.add(cls_t);
						}
					}
				}
			} else if (ch == '.') {
				// use the preceeding
				preceeding_activator = ".";
			} else if (ch == ':' && 
					idx < preTrigger.length() && 
					preTrigger.charAt(idx) == ':') {
				idx++;
				preceeding_activator = "::";
			} else if (SVCharacter.isSVIdentifierPart(ch)) {
				// Read an identifier
				StringBuffer tmp = new StringBuffer();

				tmp.append((char) ch);
				while (idx < preTrigger.length()
						&& SVCharacter.isSVIdentifierPart(
								(ch = preTrigger.charAt(idx)))) {
					tmp.append((char) ch);
					idx++;
				}
				id = tmp.toString();
				
				if (ch == '(' || ch == '\'') {
					String type_name = null;
					
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
							
							matches = finder_scopes.find(context, id, true,
									SVDBItemType.Function, SVDBItemType.Task);

							debug("first-item search for \"" + id + 
									"\" returned " + matches.size() + " matches");
							
							if (matches.size() > 0) {
								func = matches.get(0);
							}
						} else {
							search_ctxt = item_list.get(item_list.size()-1);
							
							SVDBFindByNameInClassHierarchy finder_h =
								new SVDBFindByNameInClassHierarchy(index_it, fDefaultMatcher);
							
							
							matches = finder_h.find((SVDBScopeItem)search_ctxt, 
									id, SVDBItemType.Function);
								
							debug("next-item search for \"" + id + 
									"\" in \"" + search_ctxt.getName() + 
									"\" returned " + matches.size() + " matches");
							
							func = filterByAttr(matches, preceeding_activator);

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
						type_name = id;
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

					// Only resolve this function return type of
					// it's not the last element in the string or
					// we want the type resolved
					if (idx < preTrigger.length() || resolveFinalReturnType) {
						SVDBFindByName finder_name = 
							new SVDBFindByName(index_it, fDefaultMatcher);
						
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
								new SVDBFindVarsByNameInScopes(index_it, fDefaultMatcher);
							
							matches = finder.find(context, id, true);
							
							fLog.debug("FindVarsByNameInScope \"" + context.getName() + 
									"\" returns " + matches.size() + " matches");

							if (matches.size() > 0 && matches.get(0).getType() == SVDBItemType.VarDecl) {
								SVDBVarDeclItem var_decl = (SVDBVarDeclItem)matches.get(0);
								int attr = var_decl.getTypeInfo().getAttr();
								
								if (var_decl.getTypeInfo().getParameters() != null) {
									SVDBModIfcClassDecl cls_t = pclass_finder.find(
											var_decl.getTypeInfo());
									
									if (cls_t != null) {
										matches.set(0, cls_t);
									}
								} else if ((attr & SVDBTypeInfo.TypeAttr_Queue) != 0 ||
									(attr & SVDBTypeInfo.TypeAttr_DynamicArray) != 0) {
									String base;
									if ((attr & SVDBTypeInfo.TypeAttr_Queue) != 0) {
										base = "__sv_builtin_queue";
									} else {
										base = "__sv_builtin_array";
									}
									List<SVDBModIfcClassParam> params = 
										new ArrayList<SVDBModIfcClassParam>();
									params.add(new SVDBModIfcClassParam(
											var_decl.getTypeInfo().getName()));
									SVDBTypeInfo type_info = new SVDBTypeInfo(
											base, SVDBTypeInfo.TypeAttr_Parameterized);
									type_info.setParameters(params);
									SVDBModIfcClassDecl cls_t = pclass_finder.find(type_info);
									
									if (cls_t != null) {
										matches.set(0, cls_t);
									}
								} else if ((attr & SVDBTypeInfo.TypeAttr_AssocArray) != 0) {
									String base = "__sv_builtin_assoc_array";
									List<SVDBModIfcClassParam> params = 
										new ArrayList<SVDBModIfcClassParam>();
									params.add(new SVDBModIfcClassParam(
											var_decl.getTypeInfo().getName()));
									System.out.println("Array Dim: " + var_decl.getTypeInfo().getArrayDim());
									params.add(new SVDBModIfcClassParam(
											var_decl.getTypeInfo().getArrayDim()));
									SVDBTypeInfo type_info = new SVDBTypeInfo(
											base, SVDBTypeInfo.TypeAttr_Parameterized);
									type_info.setParameters(params);
									SVDBModIfcClassDecl cls_t = pclass_finder.find(type_info);
									
									if (cls_t != null) {
										matches.set(0, cls_t);
									}
								}
							}
							
							if (matches.size() > 0 && matches.get(0).getType() == SVDBItemType.Typedef) {
								SVDBFindNamedModIfcClassIfc finder_c = 
									new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
								SVDBTypedef td = (SVDBTypedef)matches.get(0);
								
								fLog.debug("Lookup typename \"" + td.getTypeName() + "\"");
								
								List<SVDBModIfcClassDecl> cls_l = finder_c.find(td.getName());
								
								if (cls_l.size() > 0) {
									matches.set(0, cls_l.get(0));
								}
							}

							// If this is the first element and we didn't find a field,
							// then this might be a static reference. Look for a type...
							if (preceeding_activator == null &&
									(matches == null || matches.size() == 0)) {
								SVDBFindNamedModIfcClassIfc finder_c = 
									new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
								
								List<SVDBModIfcClassDecl> cls_l = finder_c.find(id);
								
								if (cls_l.size() > 0) {
									fLog.debug("Found \"" + id + "\" as a type");
									matches = new ArrayList<SVDBItem>();
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
					} else if (field instanceof SVDBVarDeclItem) {
						SVDBFindNamedModIfcClassIfc finder = 
							new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
						List<SVDBModIfcClassDecl> cl_l = finder.find(
								((SVDBVarDeclItem)field).getTypeName());
						
						type = (cl_l.size() > 0)?cl_l.get(0):null;
					} else if (field instanceof SVDBTypedef) {
						SVDBTypedef td = (SVDBTypedef)field;
						SVDBFindNamedModIfcClassIfc finder = 
							new SVDBFindNamedModIfcClassIfc(index_it, fDefaultMatcher);
						debug("field is a typedef type=\"" + td.getName() + "\" typeName=\"" + td.getTypeName() + "\"");
						
						List<SVDBModIfcClassDecl> cl_l = finder.find(td.getTypeName());
						type = (cl_l.size() > 0)?cl_l.get(0):null;
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
			} else {
				// TODO: This is actually an error (?)
				fLog.error("CHECK: ch=" + (char)ch + " is this an error?");
				return -1;
			}
		}

		debug("<-- processPreTriggerPortion(idx=" + idx + " preceeding_activator=" + preceeding_activator + ")");
		for (SVDBItem it : item_list) {
			fLog.debug("    " + it.getType() + " " + it.getName());
		}
		return idx;
	}
	
	private SVDBItem filterByAttr(List<SVDBItem> items, String trigger) {
		SVDBItem ret = null;
		
		for (SVDBItem it : items) {
			int attr = 0;
			
			if (it.getType() == SVDBItemType.Task || it.getType() == SVDBItemType.Function) {
				attr = ((SVDBTaskFuncScope)it).getAttr();
			} else if (it.getType() == SVDBItemType.VarDecl) {
				attr = ((SVDBVarDeclItem)it).getAttr();
			}
			
			if (trigger != null && trigger.equals("::")) {
				if ((attr & IFieldItemAttr.FieldAttr_Static) != 0) {
					ret = it;
					break;
				}
			} else {
				ret = it;
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
