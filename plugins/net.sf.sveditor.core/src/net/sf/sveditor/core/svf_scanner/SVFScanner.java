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


package net.sf.sveditor.core.svf_scanner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.ITextScanner;

/**
 * SVFScanner provides a scanner for the .f files that are often used to
 * specify command-line arguments to a verilog compiler.
 * 
 * @author ballance
 *
 */
public class SVFScanner {
	private LogHandle							fLog;
	private ITextScanner						fScanner;
	private List<String>						fIncludePaths;
	private Map<String, String>					fDefineMap;
	private List<String>						fFilePaths;
	private List<String>						fIncludedArgFiles;
	private static final Map<String, Boolean>	fIgnoredSwitches;
	
	static {
		fIgnoredSwitches = new HashMap<String, Boolean>();
		fIgnoredSwitches.put("-nowarn", true);
		fIgnoredSwitches.put("-32", false);
		fIgnoredSwitches.put("-64", false);
		fIgnoredSwitches.put("-work", true);
		fIgnoredSwitches.put("-error", true);
		fIgnoredSwitches.put("-warning", true);
		fIgnoredSwitches.put("-note", true);
		fIgnoredSwitches.put("-suppress", true);
		fIgnoredSwitches.put("-mfcu", false);
	}
	
	public SVFScanner() {
		fIncludePaths 	= new ArrayList<String>();
		fDefineMap 		= new HashMap<String, String>();
		fFilePaths 		= new ArrayList<String>();
		fIncludedArgFiles = new ArrayList<String>();
		
		fLog = LogFactory.getLogHandle("SVArgFileScanner");
	}
	
	public List<String> getIncludePaths() {
		return fIncludePaths;
	}
	
	public List<String> getFilePaths() {
		return fFilePaths;
	}
	
	public List<String> getArgFilePaths() {
		return fIncludedArgFiles;
	}
	
	public Map<String, String> getDefineMap() {
		return fDefineMap;
	}
	
	public void scan(ITextScanner scanner) throws Exception {
		fScanner = scanner;
		StringBuilder tmp = new StringBuilder();
		int ch;
		
		while ((ch = fScanner.skipWhite(fScanner.get_ch())) != -1) {
			if (ch == '+') {
				tmp.setLength(0);
				tmp.append((char)ch);
				
				// read a plusarg
				while ((ch = fScanner.get_ch()) != -1 && 
						ch != '=' && !Character.isWhitespace(ch)) {
					tmp.append((char)ch);
					
					if (ch == '+') {
						break;
					}
				}
				
				fLog.debug("key=" + tmp.toString());
				
				if (tmp.toString().equals("+define+")) {
					String key, val;
					tmp.setLength(0);
					
					while ((ch = fScanner.get_ch()) != -1 && 
							!Character.isWhitespace(ch) && ch != '=') {
						tmp.append((char)ch);
					}
					
					key = tmp.toString();
					
					if (ch == '=') {
						// read a value as well
						tmp.setLength(0);
						
						ch = fScanner.get_ch();
						
						if (ch == '"') {
							val = fScanner.readString(ch);
						} else {
							tmp.append((char)ch);
							while ((ch = fScanner.get_ch()) != -1 && 
									!Character.isWhitespace(ch)) {
								tmp.append((char)ch);
							}
							val = tmp.toString();
						}
					} else {
						val = "";
					}
					
					if (fDefineMap.containsKey(key)) {
						fDefineMap.remove(key);
					}
					fDefineMap.put(key, val);
				} else if (tmp.toString().equals("+incdir+")) {
					ch = fScanner.skipWhite(fScanner.get_ch());
					
					
					// Read the include path
					tmp.setLength(0);
					tmp.append((char)ch);
					do {
						while ((ch = fScanner.get_ch()) != -1 && 
								!Character.isWhitespace(ch)) {
							tmp.append((char)ch);
						}
					
						fIncludePaths.add(tmp.toString());
					} while (ch == '+');
					
					fScanner.unget_ch(ch);
				} else {
					fLog.debug("Ignoring unknown plusarg " + tmp.toString());
					// Read to the end of the string
					while ((ch = fScanner.get_ch()) != -1 &&
							!Character.isWhitespace(ch)) {}
					fScanner.unget_ch(ch);
				}
			} else if (ch == '-') {
				String key=null, val=null;
				tmp.setLength(0);
				tmp.append((char)ch);
				
				while ((ch = fScanner.get_ch()) != -1 && 
						!Character.isWhitespace(ch)) {
					tmp.append((char)ch);
				}
				
				key = tmp.toString();
				
				if (fIgnoredSwitches.containsKey(key)) {
					if (fIgnoredSwitches.get(key)) {
						// ignore next argument
						while ((ch = fScanner.get_ch()) != -1 &&
								Character.isWhitespace(ch)) {}
						fScanner.unget_ch(ch);
						while ((ch = fScanner.get_ch()) != -1 &&
								!Character.isWhitespace(ch)) {}
						fScanner.unget_ch(ch);
					}
				} else if (key.equals("-DEF") || key.toLowerCase().equals("-define")) {
					ch = fScanner.skipWhite(ch);
					
					key = fScanner.readIdentifier(ch);
					
					ch = fScanner.get_ch();
					if (ch == '=') {
						// have a value
						ch = fScanner.get_ch();
						if (ch == '"') {
							val = fScanner.readString(ch);
						} else {
							val = fScanner.readIdentifier(ch);
						}
					} else {
						val = "";
						fScanner.unget_ch(ch);
					}
					
					if (fDefineMap.containsKey(key)) {
						fDefineMap.remove(key);
					}
					fDefineMap.put(key, val);
				} else if (key.equals("-IN") || key.toLowerCase().equals("-incdir")) {
					ch = fScanner.skipWhite(fScanner.get_ch());
					
					tmp.setLength(0);
					tmp.append((char)ch);
					while ((ch = fScanner.get_ch()) != -1 && 
							!Character.isWhitespace(ch)) {
						tmp.append((char)ch);
					}

					fIncludePaths.add(tmp.toString());
				} else if (key.equals("-error") ||
						key.equals("-warning") || key.equals("-error")) {
					// Skip the next parameter

					ch = fScanner.skipWhite(fScanner.get_ch());
					while ((ch = fScanner.get_ch()) != -1 && 
							!Character.isWhitespace(ch)) {
					}
				} else if (key.equals("-f")) {
					// Add the sub-included file to the list
					
					ch = fScanner.skipWhite(ch);
					tmp.setLength(0);
					
					while (!Character.isWhitespace(ch)) {
						tmp.append((char)ch);
						ch = fScanner.get_ch();
					}
					fScanner.unget_ch(ch);
					
					fIncludedArgFiles.add(tmp.toString());
				}
			} else {
				if (ch == '/') {
					int ch2 = fScanner.get_ch();
					if (ch2 == '/') {
						while ((ch = fScanner.get_ch()) != -1 && 
								ch != '\n') {}
						fScanner.unget_ch(ch);
						continue;
					} else if (ch2 == '*') {
						int match[] = {-1, -1};
						do {
							match[0] = match[1];
							match[1] = fScanner.get_ch();
						} while ((match[0] != -1 || match[1] != -1) &&
								match[0] != '*' || match[1] != '/');
						continue;
					} else {
						fScanner.unget_ch(ch2);
					}
				}
				
				// Probably a file path
				
				tmp.setLength(0);
				tmp.append((char)ch);
				
				while ((ch = fScanner.get_ch()) != -1 &&
						!Character.isWhitespace(ch)) {
					tmp.append((char)ch);
				}
				
				fFilePaths.add(tmp.toString());
			}
		}
	}

}
