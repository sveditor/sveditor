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


package net.sf.sveditor.core.argfile.parser;

import net.sf.sveditor.core.argfile.parser.SVArgFileExprContext.ContextType;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;

public class SVArgFileExprScanner {

	private boolean 						fDebugEn = true;
	private LogHandle						fLog;
	/*
	private ISVDBFindNameMatcher			fNameMatcher;
	private SVDBFindDefaultNameMatcher		fDefaultMatcher;
	 */

	public SVArgFileExprScanner() {
		fLog = LogFactory.getLogHandle("SVArgFileExprScanner");
		/*
		fNameMatcher = matcher;
		fDefaultMatcher = new SVDBFindDefaultNameMatcher();
		 */
	}
	
	/**
	 * Extracts an expression surrounding the current scan position.
	 * 
	 * @param scanner
	 * @param leaf_scan_fwd	- Scan forward from the start point for Leaf. 
	 * @return
	 */
	public SVArgFileExprContext extractExprContext(
			IBIDITextScanner 		scanner,
			boolean					leaf_scan_fwd) {
		SVArgFileExprContext ret = new SVArgFileExprContext();
		ret.fType = ContextType.PathComplete;
		
		debug("--> extractExprContext()");

		int c = -1;
		
		boolean scan_fwd = scanner.getScanFwd();
		long scan_pos = scanner.getPos();
		scanner.setScanFwd(false);
		c = scanner.get_ch();
		debug("    First Ch (non-adjusted, scanning back): \"" + (char)c + "\"");
		scanner.seek(scan_pos);
		scanner.setScanFwd(scan_fwd);

		// We'll start by scanning backwards. On entry, the
		// cursor has been placed to read going forward
		if (scanner.getScanFwd() && scanner.getPos() > 0) {
			long pos = scanner.getPos();
			debug("    Scanning forward (pos=" + pos + ")");

			// If the previous character is whitespace, then 
			// the cursor is likely positioned at the beginning
			// of the token
			// In this case, we want to begin processing at the
			// cursor position, not one previous
			scanner.seek(pos-1);
			int prev_ch = scanner.get_ch();
			
			if (Character.isWhitespace(prev_ch) || prev_ch == '"' || 
					(SVCharacter.isSVIdentifierPart(c) && 
							!SVCharacter.isSVIdentifierPart(prev_ch))) {
				scanner.seek(pos);
			} else {
				scanner.seek(pos-1);
			}
		}
		
		scanner.setScanFwd(false);

		scan_pos = scanner.getPos();
		c = scanner.get_ch();
		debug("    First Ch (adjusted): \"" + (char)c + "\"");
		scanner.seek(scan_pos);

		// Check whether we're currently in a string
		if (isInString(scanner)) {
			debug("isInString()");
			// A string should only show up as part of a file path
			// or the argument to an option
			
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
		} else { // Not in a string
			
			// Read a ws-delimited element. This could either be 
			// an option or a path
			c = scanner.get_ch();
			
			debug("next c=" + (char)c);
			
			if (!Character.isWhitespace(c)) {
				scanner.unget_ch(c);
				c = scanner.get_ch();
				debug("re-get c=" + (char)c);
				scanner.unget_ch(c);
				String elem = readToken(scanner, leaf_scan_fwd);
				
				debug("elem=" + elem);
				
				if (elem != null && elem.length() > 0) {
					ret.fStart = (int)scanner.getPos()+1; // compensate for begin in scan-back mode
					
					if (elem.charAt(0) == '-') {
						// Content-assist for option
						ret.fLeaf = elem;
						ret.fType = ContextType.OptionComplete;
					} else if (elem.charAt(0) == '+') {
						int next_plusarg;

						if ((next_plusarg = elem.indexOf('+', 1)) != -1) {
							// The token includes another '+', indicating that
							// we have an option with a value
							ret.fRoot = elem.substring(0, next_plusarg+1);
							ret.fStart += ret.fRoot.length();
							// TODO: Setting for fStart (?)
							ret.fLeaf = elem.substring(next_plusarg+1);
						} else if ((next_plusarg = elem.indexOf('=', 1)) != -1) {
							// This is a +plusarg=<> option
							ret.fRoot = elem.substring(0, next_plusarg+1);
							ret.fStart += ret.fRoot.length();
							// TODO: Setting for fStart (?)
							ret.fLeaf = elem.substring(next_plusarg+1);
						} else {
							// mid-option. Content assist for plusarg
							ret.fLeaf = elem;
						}
					} else {
						// Should be a path
						ret.fLeaf = elem;
					}
					
					if (ret.fRoot == null) {
						// Try reading another token
						c = scanner.get_ch();
						fLog.debug("c=" + (char)c);
						if (c != -1) {
							c = scanner.skipWhite(c);
							scanner.unget_ch(c);
							debug("unget_ch=" + (char)c);
							elem = readToken(scanner, false);

							debug("elem_2=" + elem);

							if (elem != null && elem.length() > 0) {
								// plusargs not applicable here
								if (elem.charAt(0) == '-') {
									ret.fRoot = elem;
								}
							}
						}
					}
				}
			} else {
				// We're in a whitespace region. Check whether we're
				// just after an option
				
				c = scanner.skipWhite(c);
				
				if (c != -1) {
					scanner.unget_ch(c);
					String elem = readToken(scanner, leaf_scan_fwd);
					if (elem != null && elem.startsWith("-")) {
						ret.fStart = (int)scanner.getPos()+1; // compensate for begin in scan-back mode
						ret.fRoot = elem;
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
		
		fLog.debug("ret.fRoot=" + ret.fRoot + " ret.fLeaf=" + ret.fLeaf);
		
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

	private String readToken(IBIDITextScanner scanner, boolean scan_fwd) {
		int ch;
		fLog.debug("--> readToken(scan_fwd=" + scan_fwd + ") pos=" + scanner.getPos());
		
		long end_pos = (scanner.getScanFwd())?scanner.getPos():(scanner.getPos()+1);
		long start_pos = -1, seek;
		boolean is_scan_fwd = scanner.getScanFwd();
		
		// First, scan back to the beginning
		scanner.setScanFwd(false);
		while ((ch = scanner.get_ch()) != -1 &&
				!Character.isWhitespace(ch)) {
			debug("ch=" + (char)ch);
		}
		
		debug("post-scan-back ch=" + (char)ch);
	
		if (ch == -1) {
			start_pos = 0;
			seek = -1;
		} else {
			start_pos = scanner.getPos() + 2;
			seek = scanner.getPos() + 1;
		}
//		seek = scanner.getPos();
		
		if (scan_fwd) {
			scanner.setScanFwd(true);
			scanner.seek(start_pos);
			
			while ((ch = scanner.get_ch()) != -1 &&
					!Character.isWhitespace(ch)) { }
		
			fLog.debug("Changing end_pos from " + end_pos + " to " +
					(scanner.getPos()-1));
			if (ch != -1) {
				end_pos = scanner.getPos() - 1;
			} else {
				end_pos = scanner.getPos();
			}
		}

		fLog.debug("  seek " + seek);
		scanner.seek(seek);
		scanner.setScanFwd(is_scan_fwd);

		fLog.debug("<-- readToken(scan_fwd=" + scan_fwd + ") start_pos=" + start_pos + 
				" end_pos=" + end_pos);
		return scanner.get_str(start_pos, (int)(end_pos-start_pos));
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}
