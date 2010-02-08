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
	private LogHandle					fLog;
	private ITextScanner				fScanner;
	private List<String>				fIncludePaths;
	private Map<String, String>			fDefineMap;
	private List<String>				fFilePaths;
	
	
	public SVFScanner() {
		fIncludePaths 	= new ArrayList<String>();
		fDefineMap 		= new HashMap<String, String>();
		fFilePaths 		= new ArrayList<String>();
		
		fLog = LogFactory.getDefault().getLogHandle("SVArgFileScanner");
	}
	
	public List<String> getIncludePaths() {
		return fIncludePaths;
	}
	
	public List<String> getFilePaths() {
		return fFilePaths;
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
						
						while ((ch = fScanner.get_ch()) != -1 && !Character.isWhitespace(ch)) {
							tmp.append((char)ch);
						}
						val = tmp.toString();
					} else {
						val = "";
					}
					
					fDefineMap.put(key, val);
				} else if (tmp.toString().equals("+incdir+")) {
					ch = fScanner.skipWhite(fScanner.get_ch());
					
					
					// Read the include path
					tmp.setLength(0);
					tmp.append((char)ch);
					while ((ch = fScanner.get_ch()) != -1 && 
							!Character.isWhitespace(ch)) {
						tmp.append((char)ch);
					}
					
					fIncludePaths.add(tmp.toString());
				} else {
					if (ch == '=') {
						// ignore the remainder
						
						while ((ch = fScanner.get_ch()) != -1 && 
								!Character.isWhitespace(ch)) { }
					}
				}
			} else if (ch == '-') {
				String key, val;
				tmp.setLength(0);
				tmp.append((char)ch);
				
				while ((ch = fScanner.get_ch()) != -1 && 
						!Character.isWhitespace(ch)) {
					tmp.append((char)ch);
				}
				
				key = tmp.toString();
				
				// TODO: decide 
				
			} else {
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
