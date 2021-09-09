/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.argfile.parser;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.sveditor.core.SVFileUtils;
import org.sveditor.core.Tuple;
import org.sveditor.core.argfile.parser.ISVArgFileOptionProvider.OptionType;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.SVDBMarker.MarkerKind;
import org.sveditor.core.db.SVDBMarker.MarkerType;
import org.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import org.sveditor.core.db.argfile.SVDBArgFileForceSvStmt;
import org.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import org.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import org.sveditor.core.db.argfile.SVDBArgFileMfcuStmt;
import org.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import org.sveditor.core.db.argfile.SVDBArgFileSrcLibFileStmt;
import org.sveditor.core.db.argfile.SVDBArgFileSrcLibPathStmt;
import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.sveditor.core.parser.SVParseException;

public class SVArgFileParser {
	private SVArgFileOptionProviderList			fOptionProviders;
	private SVArgFileLexer						fLexer;
	private String								fFilename;
	private LogHandle							fLog;
	private boolean								fDebugEn = true;
	private List<SVDBMarker>					fMarkers;
	private ISVDBFileSystemProvider				fFSProvider;
	private String								fResolvedBaseLocation;
	private String								fBaseLocation;
	private IProject							fRootProject;
	
	public SVArgFileParser(
			String						base_location,
			String 						resolved_base_location, 
//			IProject					root_proj,
			ISVDBFileSystemProvider 	fs_provider) {
		fOptionProviders = new SVArgFileOptionProviderList();
		fOptionProviders.add(new SVArgFileQuestaOptionProvider());
		fOptionProviders.add(new SVArgFileVCSOptionProvider());
		fOptionProviders.add(new SVArgFileNCVlogOptionProvider());
		
		fLog = LogFactory.getLogHandle("SVArgFileParser");
		fResolvedBaseLocation = resolved_base_location;
		fBaseLocation = base_location;
		fFSProvider = fs_provider;
	}
	
	public void init(SVArgFileLexer lexer, String name) {
		fLexer = lexer;
		fFilename = name;
	}
	
	public SVDBFile parse(
			SVDBFile			file,
			List<SVDBMarker> 	markers) throws SVParseException {
		
		fMarkers = markers;
	
		if (fDebugEn) {
			fLog.debug("--> parse() " + fFilename);
		}
		
		while (fLexer.peek() != null) {
			if (fLexer.isOption()) {
				// Recognize the special-case -SVE_SET_CWD option
				if (fLexer.peek().equals("-SVE_SET_CWD")) {
					// Reset the working directory
					fLexer.consumeToken();
					fBaseLocation = fLexer.readPath();
					fResolvedBaseLocation = fBaseLocation;
				} else {
					SVArgFileToken tok = fLexer.consumeToken();
					OptionType type = fOptionProviders.getOptionType(tok.getImage());
					int arg_count = fOptionProviders.optionArgCount(tok.getImage());
					
					if (fDebugEn) {
						fLog.debug("  isOption: " + tok.getImage() + " type=" + type + 
								" arg_count=" + arg_count);
					}
					
					// Determine what type of option this is
					switch (type) {
						case Unrecognized: {
							// Treat plus-args as zero-option switches
							// Treat dash-args are one-option switches
							if (tok.getImage().startsWith("-")) {
								fLexer.eatToken();
							}
							} break;
						
							// Recognized, but ignored, option
						case Ignored: {
							// TODO: Consume known options
							for (int i=0; i<arg_count; i++) {
								fLexer.eatToken();
							}
							} break;
							
						case Incdir: {
							List<String> inc_path_l = null;
							long loc = fLexer.getStartLocation();
							
							if (arg_count > 0) {
								// include path is the argument
								String path = fLexer.readPath();
								inc_path_l = fOptionProviders.getIncPaths(tok.getImage(), path);
							} else {
								inc_path_l = fOptionProviders.getIncPaths(
										tok.getImage(), 
										tok.getOptionVal());
							}

							if (inc_path_l != null) {
								for (String path : inc_path_l) {
									path = SVFileUtils.resolvePath(path, 
											fResolvedBaseLocation, fFSProvider, true);

									if (!fFSProvider.isDir(path)) {
										error(tok.getStartLocation(), "Include path \"" + path + "\" does not exist. " +
												"Resolved relative to \"" + fResolvedBaseLocation + "\"");
									}
									SVDBArgFileIncDirStmt stmt = new SVDBArgFileIncDirStmt();
									stmt.setLocation(loc);
									stmt.setIncludePath(path);
									file.addChildItem(stmt);
								}
							} else {
								error(tok.getStartLocation(), "No include-file path provided");
							}
							} break;
							
						case Define: {
							SVDBArgFileDefineStmt stmt = new SVDBArgFileDefineStmt();
							stmt.setLocation(fLexer.getStartLocation());
							Tuple<String, String> def;
							
							if  (arg_count > 0) {
								// Define is the argument
								def = fOptionProviders.getDefValue(
										tok.getImage(),
										fLexer.readPath());
							} else {
								String val = (tok.getOptionVal() != null)?tok.getOptionVal():"";
								def = fOptionProviders.getDefValue(tok.getImage(), val);
							}
							
							stmt.setKey(def.first());
							stmt.setValue(def.second());
							
							file.addChildItem(stmt);
							} break;
							
						case ArgFileInc: 
						case ArgFileRootInc: {
							SVDBArgFileIncFileStmt stmt = new SVDBArgFileIncFileStmt();
							stmt.setLocation(tok.getStartLocation());
							List<String> incs;
							
						
							// Flag the root-include status
							stmt.setRootInclude((type == OptionType.ArgFileRootInc));
							
							if (arg_count > 0) {
								incs = fOptionProviders.getArgFilePaths(
										tok.getImage(), fLexer.readPath());
							} else {
								incs = fOptionProviders.getArgFilePaths(
										tok.getImage(),
										tok.getOptionVal());
							}
							
							if (incs == null || incs.size() == 0) {
								error(tok.getStartLocation(), "No argument-file path provided");
							} else {
								String inc = incs.get(0);
								
								if (inc != null) {
									String path = SVFileUtils.resolvePath(incs.get(0),
											fResolvedBaseLocation, fFSProvider, true);
									if (!fFSProvider.fileExists(path)) {
										error(tok.getStartLocation(), 
												"Argument-file path \"" + path + "\" does not exist; " +
														"Resolved relative to \"" + fResolvedBaseLocation + "\"");
									}
									stmt.setPath(path);
								} else {
									error(tok.getStartLocation(), "No argument-file path provided");
									stmt.setPath("");
								}
								file.addChildItem(stmt);
							}
							} break;
							
						case MFCU: {
							SVDBArgFileMfcuStmt stmt = new SVDBArgFileMfcuStmt();
							stmt.setLocation(fLexer.getStartLocation());
							
							file.addChildItem(stmt);
							} break;
							
						case SrcLibPath: {
							SVDBArgFileSrcLibPathStmt stmt = new SVDBArgFileSrcLibPathStmt();
							stmt.setLocation(fLexer.getStartLocation());
							
							String path = fLexer.readPath();
							path = SVFileUtils.resolvePath(path, fResolvedBaseLocation, 
									fFSProvider, true);
							if (!fFSProvider.isDir(path)) {
								error(tok.getStartLocation(),
										"Source library path \"" + path + "\" does not exist; " + 
											"Resolved relative to \"" + fResolvedBaseLocation + "\"");
							}
							stmt.setSrcLibPath(path);
							file.addChildItem(stmt);
							} break;
							
						case SrcLibFile: {
							SVDBArgFileSrcLibFileStmt stmt = new SVDBArgFileSrcLibFileStmt();
							stmt.setLocation(fLexer.getStartLocation());
							
							String path = fLexer.readPath();
							path = SVFileUtils.resolvePath(path, fResolvedBaseLocation, 
									fFSProvider, true);
							if (!fFSProvider.fileExists(path)) {
								error(tok.getStartLocation(),
										"Source library file \"" + path + "\" does not exist; " + 
											"Resolved relative to \"" + fResolvedBaseLocation + "\"");
							}
							stmt.setSrcLibFile(path);
							file.addChildItem(stmt);
							} break;
							
						case SV: {
							SVDBArgFileForceSvStmt stmt = new SVDBArgFileForceSvStmt();
							stmt.setLocation(fLexer.getStartLocation());
							
							file.addChildItem(stmt);
						} break;
							
						default:
							error(tok.getStartLocation(), "Unrecognized option type " + type);
							break;
					}					
				}
			} else {
				// It's a path
				SVDBArgFilePathStmt p = new SVDBArgFilePathStmt();
				long loc = fLexer.getStartLocation();
				p.setLocation(loc);
				String path = fLexer.eatToken();
				file.addChildItem(p);
				
				// Try to resolve path
				path = SVFileUtils.resolvePath(path, fResolvedBaseLocation,
						fFSProvider, true);
				p.setPath(path);
				
				if (!fFSProvider.fileExists(path)) {
					error(loc, "Path \"" + path + "\" does not exist; " + 
						"Resolved relative to \"" + fResolvedBaseLocation + "\"");
				} else if (fFSProvider.isDir(path)) {
					error(loc, "Path \"" + path + "\" is a directory, not a file");
				}
			}
		}
		
		fLog.debug("<-- parse() " + fFilename);
		
		return file;
	}
	
	private void error(long location, String msg) throws SVParseException {
		if (fMarkers != null) {
			SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.UndefinedMacro, msg);
			m.setLocation(location);
			fMarkers.add(m);
		}
//		System.out.println("[ERROR] " + msg);
	}
}
