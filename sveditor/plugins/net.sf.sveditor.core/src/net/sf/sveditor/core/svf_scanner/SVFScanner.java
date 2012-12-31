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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
	private List<String>						fLibPaths;
	private static Set<String>					fSrcExtensions;
	private List<String>						fIncludedArgFiles;
	public static final Map<String, Integer>	fIgnoredSwitches;
	public static final Set<String>			fSupportedSwitches;
	public static final Set<String>			fRecognizedSwitches;
	
	static {
		fIgnoredSwitches = new HashMap<String, Integer>();
		fIgnoredSwitches.put("-nowarn", 1);
		fIgnoredSwitches.put("-time", 0);
		fIgnoredSwitches.put("-version", 0);
		fIgnoredSwitches.put("-32", 0);
		fIgnoredSwitches.put("-64", 0);
		fIgnoredSwitches.put("-work", 1);
		fIgnoredSwitches.put("-error", 1);
		fIgnoredSwitches.put("-warning", 1);
		fIgnoredSwitches.put("-note", 1);
		fIgnoredSwitches.put("-suppress", 1);
		fIgnoredSwitches.put("-msglimit", 1);
		fIgnoredSwitches.put("-compat", 0);
		fIgnoredSwitches.put("-ccflags", 1);
		fIgnoredSwitches.put("-compile_uselibs", 0);
		fIgnoredSwitches.put("-coveropt", 1);
		fIgnoredSwitches.put("-coverexcludedefault", 0);
		fIgnoredSwitches.put("-coverfec", 0);
		fIgnoredSwitches.put("-nocoverfec", 0);
		fIgnoredSwitches.put("-coverudp", 0);
		fIgnoredSwitches.put("-covershort", 0);
		fIgnoredSwitches.put("-nocoverexcludedefault", 0);
		fIgnoredSwitches.put("-covercells", 0);
		fIgnoredSwitches.put("-nocovercells", 0);
		fIgnoredSwitches.put("-constimmedassert", 0);
		fIgnoredSwitches.put("-togglecountlimit", 1);
		fIgnoredSwitches.put("-togglewidthlimit", 1);
		fIgnoredSwitches.put("-extendedtogglemode", 1);
		fIgnoredSwitches.put("-toggleportsonly", 0);
		fIgnoredSwitches.put("-maxudprows", 1);
		fIgnoredSwitches.put("-maxfecrows", 1);
		fIgnoredSwitches.put("-coverrportcancelleded", 0);
		fIgnoredSwitches.put("-deglitchalways", 0);
		fIgnoredSwitches.put("-dpiforceheader", 0);
		fIgnoredSwitches.put("-dpiheader", 1);
		fIgnoredSwitches.put("-E", 1);
		fIgnoredSwitches.put("-Epretty", 1);
		fIgnoredSwitches.put("-Edebug", 1);
		fIgnoredSwitches.put("-enumfirstinit", 0);
		fIgnoredSwitches.put("-nofsmresettrans", 0);
		fIgnoredSwitches.put("-fsmresettrans", 0);
		fIgnoredSwitches.put("-nofsmsingle", 0);
		fIgnoredSwitches.put("-fsmsingle", 0);
		fIgnoredSwitches.put("-fsmimplicittrans", 0);
		fIgnoredSwitches.put("-nofsmimplicittrans", 0);
		fIgnoredSwitches.put("-fsmmultitrans", 0);
		fIgnoredSwitches.put("-fsmverbose", 1);
		fIgnoredSwitches.put("-nofsmxassign", 0);
		fIgnoredSwitches.put("-fsmxassign", 0);
		fIgnoredSwitches.put("-gen_xml", 2);
		fIgnoredSwitches.put("-hazards", 0);
		fIgnoredSwitches.put("-incr", 0);
		fIgnoredSwitches.put("-L", 1);
		fIgnoredSwitches.put("-Lf", 1);
		fIgnoredSwitches.put("-l", 1);
		fIgnoredSwitches.put("-libmap", 1);
		fIgnoredSwitches.put("-libmap_verbose", 0);
		fIgnoredSwitches.put("-line", 1);
		fIgnoredSwitches.put("-lint", 0);
		fIgnoredSwitches.put("-lowercasepragma", 0);
		fIgnoredSwitches.put("-lowercasepslpragma", 0);
		fIgnoredSwitches.put("-lrmclassinit", 0);
		fIgnoredSwitches.put("-modelsimini", 1);
		fIgnoredSwitches.put("-modelsimini", 1);
		fIgnoredSwitches.put("-mfcu", 0);
		fIgnoredSwitches.put("-nocheck", 0);
		fIgnoredSwitches.put("-nodebug", 0);
		fIgnoredSwitches.put("-nodbgsym", 0);
		fIgnoredSwitches.put("-noincr", 0);
		fIgnoredSwitches.put("-nologo", 0);
		fIgnoredSwitches.put("-nopsl", 0);
		fIgnoredSwitches.put("-novopt", 0);
		fIgnoredSwitches.put("-nowarn", 1);
		fIgnoredSwitches.put("-noconstimmedassert", 0);
		fIgnoredSwitches.put("-O0", 0);
		fIgnoredSwitches.put("-O1", 0);
		fIgnoredSwitches.put("-O4", 0);
		fIgnoredSwitches.put("-O5", 0);
		fIgnoredSwitches.put("-pedanticerrors", 0);
		fIgnoredSwitches.put("-permissive", 0);
		fIgnoredSwitches.put("-printinfilenames", 0);
		fIgnoredSwitches.put("-pslext", 0);
		fIgnoredSwitches.put("-pslfile", 1);
		fIgnoredSwitches.put("-quiet", 0);
		// skipping -R ... -
		fIgnoredSwitches.put("-refresh", 0);
		fIgnoredSwitches.put("-scdpiheader", 1);
		fIgnoredSwitches.put("-sfcu", 0);
		fIgnoredSwitches.put("-skipprotected", 0);
		fIgnoredSwitches.put("-skipprotectedmodule", 0);
		fIgnoredSwitches.put("-source", 0);
		fIgnoredSwitches.put("-sv", 0);
		fIgnoredSwitches.put("-sv05compat", 0);
		fIgnoredSwitches.put("-sv09compat", 0);
		fIgnoredSwitches.put("-oldsv", 0);
//		fIgnoredSwitches.put("-svimportport=", 0);
		fIgnoredSwitches.put("-timescale", 1);
		fIgnoredSwitches.put("-override_timescale", 1);
		fIgnoredSwitches.put("-u", 0);
		// TODO: handle -v switch ?
		fIgnoredSwitches.put("-v", 1);
		fIgnoredSwitches.put("-vlog96compat", 0);
		fIgnoredSwitches.put("-vlog01compat", 0);
		fIgnoredSwitches.put("-convertallparams", 0);
		fIgnoredSwitches.put("-mixedsvvh", 1);
		fIgnoredSwitches.put("-vopt", 0);
		fIgnoredSwitches.put("-vmake", 0);
		fIgnoredSwitches.put("-writetoplevels", 0);
//		fIgnoredSwitches.put("-y", 1);
		
		fSupportedSwitches = new HashSet<String>();
		fSupportedSwitches.add("+define+");
		fSupportedSwitches.add("-DEF");
		fSupportedSwitches.add("-define");
		fSupportedSwitches.add("+incdir+");
		fSupportedSwitches.add("-IN");
		fSupportedSwitches.add("-incdir");
		fSupportedSwitches.add("-y");
		fSupportedSwitches.add("-v");
		fSupportedSwitches.add("-f");
		fSupportedSwitches.add("-file");
		
		
		fRecognizedSwitches = new HashSet<String>();
		fRecognizedSwitches.addAll(fIgnoredSwitches.keySet());
		fRecognizedSwitches.addAll(fSupportedSwitches);
		
		fSrcExtensions		= new HashSet<String>();
		
		fSrcExtensions.add(".sv");
		fSrcExtensions.add(".v");
		fSrcExtensions.add(".vl");
		fSrcExtensions.add(".vlog");
	}
	
	public SVFScanner() {
		fIncludePaths 		= new ArrayList<String>();
		fDefineMap 			= new HashMap<String, String>();
		fFilePaths 			= new ArrayList<String>();
		fLibPaths			= new ArrayList<String>();
		fIncludedArgFiles 	= new ArrayList<String>();
		
		fLog = LogFactory.getLogHandle("SVArgFileScanner");
	}
	
	public List<String> getIncludePaths() {
		return fIncludePaths;
	}
	
	public List<String> getFilePaths() {
		return fFilePaths;
	}
	
	public List<String> getLibPaths() {
		return fLibPaths;
	}
	
	public static Set<String> getSrcExts() {
		return fSrcExtensions;
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
					int ignore_arg_count = fIgnoredSwitches.get(key);
					for (int i=0; i<ignore_arg_count; i++) {
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
				} else if (key.equals("-f") || key.equals("-file")) {
					// Add the sub-included file to the list
					
					ch = fScanner.skipWhite(ch);
					tmp.setLength(0);
					
					while (ch != -1 && !Character.isWhitespace(ch)) {
						tmp.append((char)ch);
						ch = fScanner.get_ch();
					}
					fScanner.unget_ch(ch);
					
					fIncludedArgFiles.add(tmp.toString());
				} else if (key.equals("-v")) {
					// Verilog library file. Treat as a regular file
					ch = fScanner.skipWhite(ch);
					tmp.setLength(0);
					
					while (!Character.isWhitespace(ch)) {
						tmp.append((char)ch);
						ch = fScanner.get_ch();
					}
					fScanner.unget_ch(ch);
					fFilePaths.add(tmp.toString());
				} else if (key.equals("-y")) {
					
					ch = fScanner.skipWhite(ch);
					tmp.setLength(0);
					tmp.append((char)ch);
					
					while ((ch = fScanner.get_ch()) != -1 &&
							!Character.isWhitespace(ch)) {
						tmp.append((char)ch);
					}
					
					fLibPaths.add(tmp.toString());
				}
			} else if (ch == '#') {
				// Skip preprocessor like lines such as #ifndef, #endif
				while ((ch = fScanner.get_ch()) != -1 && 
						ch != '\n') {}
				fScanner.unget_ch(ch);
				continue;
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
			
				String path = tmp.toString();
				path = path.trim();
				if(!path.matches(".*\\.(c|h|cpp|hpp)$")){
					fFilePaths.add(path);
				}
			}
		}
	}

}
