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


package net.sf.sveditor.core.expr_utils;

import net.sf.sveditor.core.expr_utils.SVExprContext.ContextType;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class SVExprScanner {

	private boolean 						fDebugEn = true;
	private LogHandle						fLog;
	/*
	private ISVDBFindNameMatcher			fNameMatcher;
	private SVDBFindDefaultNameMatcher		fDefaultMatcher;
	 */

	public SVExprScanner() {
		fLog = LogFactory.getLogHandle("SVExprScanner");
		/*
		fNameMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
		 */
	}
	
/*
	public void setMatcher(ISVDBFindNameMatcher matcher) {
		fNameMatcher = matcher;
	}
	 */

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
		c = scanner.get_ch();
		debug("    First Ch (non-adjusted): \"" + (char)c + "\"");
		scanner.unget_ch(c);
		scanner.setScanFwd(scan_fwd);

		// We'll start by scanning backwards. On entry, the
		// cursor has been placed to read going forward
		if (scanner.getScanFwd() && scanner.getPos() > 0) {
			debug("    Scanning forward");
			/*
			debug("Adjust position: old=\"" + scanner.get_str(scanner.getPos(), 1) + "\" new=\"" +
					scanner.get_str(scanner.getPos()-1, 1) + "\"");
			 */
			long pos = scanner.getPos();

			// If the previous character is whitespace, then 
			// the cursor is likely positioned at the beginning
			// of the token
			// In this case, we want to begin processing at the
			// cursor position, not one previous
			scanner.seek(pos-1);
			int prev_ch = scanner.get_ch();
			
			debug("      prev_ch=" + (char)prev_ch);
			
			if (Character.isWhitespace(prev_ch) || prev_ch == '"' || 
					(SVCharacter.isSVIdentifierPart(c) && 
							!SVCharacter.isSVIdentifierPart(prev_ch))) {
				// Consider 
				if (prev_ch == '"' && (c == '\n' || c == '\r')) {
					scanner.seek(pos-1);
				} else {
					scanner.seek(pos);
				}
			} else {
				scanner.seek(pos-1);
			}
		}
		
		scanner.setScanFwd(false);
	
		c = scanner.get_ch();
		debug("    First Ch (adjusted): \"" + (char)c + "\"");
		scanner.unget_ch(c);

		// Check whether we're currently in a string
		if (isInString(scanner)) {
			debug("isInString()");
			// It's most likely that we're looking at an include
			
			ret.fType = ContextType.String;

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
				String id = scanner.readIdentifier(c);
				debug("id=\"" + id + "\"");
				
				c = scanner.skipWhite(scanner.get_ch());
				
				debug("next=\"" + (char)c + "\"");
				
				if (c == '`' && id.equals("include")) {
					ret.fTrigger = "`";
					ret.fRoot = "include";
				}
			}
		} else { // Not in a string
			if (SVCharacter.isSVIdentifierPart((c = scanner.get_ch()))) {
				debug("notInString c=\"" + (char)c + "\"");
				scanner.unget_ch(c);
				String id = readIdentifier(scanner, leaf_scan_fwd);
				ret.fStart = (int)scanner.getPos()+1; // compensate for begin in scan-backward mode
				ret.fLeaf = id;
				
				debug("id=\"" + id + "\"");

				// See if we're working with a triggered expression
				ret.fTrigger = readTriggerStr(scanner, true);
				debug("trigger=\"" + ret.fTrigger + "\"");
				
				if (ret.fTrigger != null && !ret.fTrigger.equals("`")) {
					// Read an expression
					ret.fType = ContextType.Triggered;
					ret.fRoot = readExpression(scanner);
					
					if (ret.fRoot != null && ret.fRoot.trim().equals("")) {
						ret.fRoot = null;
					}
				} else if (ret.fTrigger == null) {
					ret.fType = ContextType.Untriggered;
						
					// Just process the identifier
					c = scanner.skipWhite(scanner.get_ch());
					
					if (c == '=') {
						int c2 = scanner.get_ch();
						if (c2 != '=' && c2 != '>' &&
								c2 != '<' && c2 != '&' &&
								c2 != '|' && c2 != '+' &&
								c2 != '-' && c2 != '!') {
							c = scanner.skipWhite(c2);
							ret.fTrigger = "=";
						}
					}
					
					if (SVCharacter.isSVIdentifierPart(c)) {
						scanner.unget_ch(c);
						ret.fRoot = readIdentifier(scanner, false);
					} else {
						// Default back to untriggered 
						ret.fTrigger = null;
						ret.fType = ContextType.Untriggered;
					}
				}
			} else { // Not an identifier part
				// backup and try for a triggered identifier
				debug("notInId: ch=\"" + (char)c + "\"");
				
				scanner.unget_ch(c);
				
				ret.fStart = (int)scanner.getPos()+1; // compensate for begin in scan-backward mode
				
				if ((ret.fTrigger = readTriggerStr(scanner, true)) != null) {
					ret.fType = ContextType.Triggered;
					
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
				} else {
					// Back up to see if there's an include previously
					scanner.seek(ret.fStart);
					c = scanner.skipWhite(c);
					
//					int ch2 = scanner.get_ch();
//					int ch3 = scanner.get_ch();
					
//					debug("notInTriggered: c=\"" + (char)c + "\" ch2=" + (char)ch2 + " ch3=" + (char)ch3);
					debug("notInTriggered: scanFwd=" + scanner.getScanFwd());
					
					scanner.unget_ch(c);
					
					String id = readIdentifier(scanner, false);
					
					debug("notInTriggered: id=\"" + id + "\"");
					
					if (id != null && 
							(id.equals("include") ||
							 id.equals("extends") ||
							 id.equals("import")
							)) {
						if (ret.fStart > 0) {
							ret.fStart--;
						}
						
						if (id.equals("include")) {
							ret.fTrigger = "`";
						}
						ret.fRoot = id;
						ret.fLeaf = "";
					}
				}
			}
		}
		
		if (ret.fType != ContextType.String) {
			if (ret.fRoot != null) {
				if (ret.fRoot.equals("import")) {
					ret.fType = ContextType.Import;
				} else if (ret.fRoot.equals("extends")) {
					ret.fType = ContextType.Extends;
				}
			} else {
				// Read preceeding token. It's possible we need to change this type
				c = scanner.skipWhite(scanner.get_ch());

				if (SVCharacter.isSVIdentifierPart(c)) {
					scanner.unget_ch(c);
					String tmp = readIdentifier(scanner, false);
					
					fLog.debug("preceeding token: " + tmp.toString());
						
					if (tmp.equals("import")) {
						ret.fType = ContextType.Import;
					} else if (tmp.equals("extends")) {
						ret.fType = ContextType.Extends;
					}
				}
			}
		}
		
		debug("<-- extractExprContext()");
		
		if (ret.fRoot != null && ret.fRoot.trim().equals("")) {
			ret.fRoot = null;
		}
		
		if (ret.fRoot == null && ret.fTrigger == null && ret.fLeaf == null) {
			ret.fLeaf = "";
		}
		
		return ret;
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
				// Could be a function
				fLog.debug("    post ')(' char is: " + (char)ch);
				ch = scanner.skipWhite(scanner.get_ch());
				if (SVCharacter.isSVIdentifierPart(ch)) {
					scanner.readIdentifier(ch);
				} else {
					scanner.unget_ch(ch);
				}
			} else if (ch == ']') {
				// Skip what's in an array reference
				ch = scanner.skipPastMatch("][");
				ch = scanner.skipWhite(scanner.get_ch());
				if (SVCharacter.isSVIdentifierPart(ch)) {
					scanner.readIdentifier(ch);
				} else {
					scanner.unget_ch(ch);
				}
			} else if (SVCharacter.isSVIdentifierPart(ch)) {
				scanner.readIdentifier(ch);
			} else {
				fLog.debug("end readExpression: unknown ch \"" + (char)ch + "\"");
				start_pos = (scanner.getPos()+2);
				break;
			}
			start_pos = (scanner.getPos()+1);
			trigger = readTriggerStr(scanner, false);
			
			if (trigger == null) {
				break;
			} else if (trigger.equals("`")) {
				start_pos = (scanner.getPos()+1);
				trigger = readTriggerStr(scanner, false);
				if (trigger == null) {
					break;
				}
			}
		} while (true); // ((trigger = readTriggerStr(scanner, false)) != null);
		
		fLog.debug("<-- readExpression");
	
		return scanner.get_str(start_pos, (int)(end_pos-start_pos+1)).trim();
	}

	/**
	 * 
	 * @param scanner
	 * @return
	 */
	private String readTriggerStr(IBIDITextScanner scanner, boolean allow_colon) {
		long start_pos = scanner.getPos();
		scanner.setScanFwd(false);
		int ch = scanner.skipWhite(scanner.get_ch());
		
		if (ch == '.' || ch == '`') {
			return "" + (char)ch;
		} else if (ch == ':') {
			int ch2 = scanner.get_ch();
			
			if (ch2 == ':') {
				return "::";
			} else if (allow_colon) {
				return ":";
			}
		}
		
		// If we didn't identify a trigger, then restore the
		// previous position
		scanner.seek(start_pos);
		return null;
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
		while ((ch = scanner.get_ch()) != -1) {
//MSB			System.out.println("ch=" + (char)ch);
			if (!SVCharacter.isSVIdentifierPart(ch)) { 
				break;
			}
		}
				
		
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

	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(ILogLevel.LEVEL_MID, msg);
		}
	}
}
