package net.sf.sveditor.core.preproc;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.SVFileBuffer;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.SVDBIndexStats;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IPreProcErrorListener;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcessor2 extends AbstractTextScanner 
		implements ISVPreProcessor, ILogLevelListener, IPreProcErrorListener {
	private SVDBIndexStats							fIndexStats;
	private ISVPreProcIncFileProvider				fIncFileProvider;
	private StringBuilder							fOutput;
	private int										fOutputLen;
	private StringBuilder							fCommentBuffer;
	private boolean									fInComment;
	private IDocCommentParser   					fDocCommentParser;
	private ScanLocation							fCommentStart;

	// List of offset,file-id pairs
	private List<SVPreProcOutput.FileChangeInfo>	fFileMap;
	private List<String>							fFileList;
	private StringBuilder							fTmpBuffer;
	private List<Tuple<String, String>>				fParamList;
	private Stack<Integer>							fPreProcEn;
	private Stack<ScanLocation>						fPreProcLoc;
	private IPreProcMacroProvider					fMacroProvider;
	private SVPreProcDefineProvider					fDefineProvider;
	private LogHandle								fLog;
	private boolean									fDebugEn = false;
	
	private Stack<SVPreProc2InputData>				fInputStack;
	private SVPreProc2InputData						fInputCurr;
	private ISVPreProcFileMapper					fFileMapper;
	private Map<String, SVDBMacroDef>				fMacroMap = new HashMap<String, SVDBMacroDef>();
	
	private static final int    PP_DISABLED 			= 0;
	private static final int    PP_ENABLED  			= 1;
	
	// This bit is set when we are within a disabled section.
	// It's impossible for anything in a sub-section to be enabled
	private static final int    PP_CARRY    			= 2;
	
	// This bit is set when a block within this level of conditionals
	// has been taken (ie `ifdef (true) ... ; `ifndef (false))
	private static final int	PP_THIS_LEVEL_EN_BLOCK 	= 4;
	
	public static final Set<String>	fIgnoredDirectives;

	static {
		fIgnoredDirectives = new HashSet<String>();
		fIgnoredDirectives.add("begin_keywords");
		fIgnoredDirectives.add("celldefine");
		fIgnoredDirectives.add("default_nettype");
		fIgnoredDirectives.add("end_keywords");
		fIgnoredDirectives.add("endcelldefine");
		fIgnoredDirectives.add("protect");
		fIgnoredDirectives.add("endprotect");
		// Ignored for now
		fIgnoredDirectives.add("line");
		fIgnoredDirectives.add("nounconnected_drive");
		fIgnoredDirectives.add("noportcoerce");
		fIgnoredDirectives.add("timescale");
		// Ignored for now
		fIgnoredDirectives.add("resetall");
		fIgnoredDirectives.add("unconnected_drive");
		//
		fIgnoredDirectives.add("disable_portfaults");
		fIgnoredDirectives.add("enable_portfaults");
		fIgnoredDirectives.add("nosuppress_faults");
		fIgnoredDirectives.add("suppress_faults");
		// Ignored for now
		fIgnoredDirectives.add("undef");
		fIgnoredDirectives.add("undefineall");
	}

	public SVPreProcessor2(
			String							filename,
			InputStream	 					input, 
			ISVPreProcIncFileProvider		inc_provider,
			ISVPreProcFileMapper			file_mapper) {
		fInputStack = new Stack<SVPreProc2InputData>();
		fOutput = new StringBuilder();
		fCommentBuffer = new StringBuilder();
		fDocCommentParser = new DocCommentParser();
		fTmpBuffer = new StringBuilder();
		fParamList = new ArrayList<Tuple<String,String>>();
		fPreProcEn = new Stack<Integer>();
		fPreProcLoc = new Stack<ScanLocation>();
		fFileMap = new ArrayList<SVPreProcOutput.FileChangeInfo>();
		fFileList = new ArrayList<String>();

		fIncFileProvider 	= inc_provider;
		fFileMapper			= file_mapper;
	
		fMacroProvider  = defaultMacroProvider;
		defaultMacroProvider.setMacro("SVEDITOR", "");
		fDefineProvider = new SVPreProcDefineProvider(fMacroProvider);
		fDefineProvider.addErrorListener(this);
		
		fLog = LogFactory.getLogHandle("SVPreProcessor2");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
	
		// Add the first file
		enter_file(filename, input);
	}
	
	public Collection<SVDBMacroDef> getDefaultMacros() {
		return fMacroMap.values();
	}
	
	public void setIndexStats(SVDBIndexStats stats) {
		fIndexStats = stats;
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	public void setMacroProvider(IPreProcMacroProvider mp) {
		fMacroProvider = mp;
		fDefineProvider.setMacroProvider(mp);
	}
	
	public IPreProcMacroProvider getMacroProvider() {
		return fMacroProvider;
	}
	
	public SVPreProcOutput preprocess() {
		int ch, last_ch = -1;
		int end_comment1 = -1, end_comment2 = -1;
		long start, end;
		boolean in_string = false;
		boolean ifdef_enabled = true;
		boolean found_single_line_comment = false;
		
		start = System.currentTimeMillis();

		while ((ch = get_ch()) != -1) {
			found_single_line_comment = false;
			if (!in_string) {
				// Handle comment
				if (ch == '/') {
					int ch2 = get_ch();

					if (ch2 == '/') {
						output(' ');
						found_single_line_comment = true;
						beginComment();
						while ((ch = get_ch()) != -1 && 
								ch != '\n' && ch != '\r') { 
							fCommentBuffer.append((char)ch);
						}
						fCommentBuffer.append('\n');

						// Handle
						if (ch == '\r') {
							ch = get_ch();
							if (ch != '\n') {
								unget_ch(ch);
							}
						}
						ch = '\n';
						last_ch = ' ';
					} else if (ch2 == '*') {
						end_comment1 = -1;
						end_comment2 = -1;

						output(' ');

						beginComment();
						while ((ch = get_ch()) != -1) {
							end_comment1 = end_comment2;
							end_comment2 = ch;

							if (end_comment1 == '*' && end_comment2 == '/') {
								endComment();
								break;
							} else {
								fCommentBuffer.append((char)ch);
							}
						}
						ch = ' ';
						last_ch = ' ';
					} else {
						unget_ch(ch2);
					}
				}
				
				if (!Character.isWhitespace(ch) && fInComment) {
					// Send accumlated comment to observer
					endComment();
				}
				
				if (ch == '`') {
					// Processing an ifdef may affect enablement
					handle_preproc_directive();
					ifdef_enabled = ifdef_enabled();
					if (!ifdef_enabled) {
						output(' ');
					}
				} else {
					if (ch == '"' && last_ch != '\\') {
						// Enter string
						in_string = true;
					}
					if (ifdef_enabled) {
						output((char)ch);
					}
				}
			} else {
				// In String
				if (ch == '"' && last_ch != '\\') {
					in_string = false;
				}
				if (ifdef_enabled) {
					output((char)ch);
				}
			}
			
			// Consecutive back-slashes convert to
			// a single backslash. For tracking purposes,
			// convert to space
			if (last_ch == '\\' && ch == '\\') {
				last_ch = ' ';
			} else {
				last_ch = ch;
			}
			
			if (fInComment && !found_single_line_comment && ch == '\n') {
				endComment();
			}
		}
		
		SVPreProcOutput ret = new SVPreProcOutput(
				fOutput, null, fFileMap, fFileList);
		ret.setFileTree(fInputCurr.getFileTree());
		
		// Clean up after any unbalanced pre-processor directives
		cleanup_preproc_leftovers();
	
		// Leave final file
		fInputCurr.close();
		
		// Finally, save the full pre-processor state to the final file
		/*
		last_file.fFileTree.fDefinedMacros.clear();
		for (Entry<String, SVDBMacroDef> e : fMacroMap.entrySet()) {
			if (!e.getKey().equals("__FILE__") && !e.getKey().equals("__LINE__")) {
				last_file.fFileTree.fDefinedMacros.put(e.getKey(), e.getValue());
			}
		}
		 */
		
		end = System.currentTimeMillis();
		
		if (fIndexStats != null) {
			if (fInputCurr.getInput() instanceof SVFileBuffer) {
				fIndexStats.incLastIndexFileReadTime(
						((SVFileBuffer)fInputCurr.getInput()).getReadTime());
			}
			fIndexStats.incNumLines(fInputCurr.getLineCount());
			fIndexStats.incLastIndexPreProcessTime(end-start);
			fIndexStats.incNumProcessedFiles();
		}
		
		return ret;
	}
	
	public SVDBFileTree getFileTree() {
		return fInputCurr.getFileTree();
	}
	
	public SVPreProc2InputData currentRealFile() {
		int i=fInputStack.size()-1;
		
		while (i>=0 && fInputStack.get(i).getFileId() == -1) {
			i--;
		}
		
		if (i >= 0) {
			return fInputStack.get(i);
		} else {
			return null;
		}
	}
	
	private void beginComment() {
		if (!fInComment) {
			fCommentBuffer.setLength(0);
			fCommentStart = getLocation();
		}
		fInComment = true;
	}
	
	private void endComment() {
		if(!fInComment) { return ; }
		fInComment = false ;
		String comment = fCommentBuffer.toString() ;
		String title = fDocCommentParser.isDocComment(comment) ;
		if (title != null) {
			SVPreProc2InputData in = fInputCurr;
			SVDBDocComment doc_comment = new SVDBDocComment(title, comment);
			SVDBLocation loc = new SVDBLocation(fCommentStart.getFileId(),  
					fCommentStart.getLineNo(), fCommentStart.getLinePos());
			doc_comment.setLocation(loc);
			if (in.getFileTree() != null) {
				in.getFileTree().getSVDBFile().addChildItem(doc_comment);
			}
		}		
	}
	
	private void handle_preproc_directive() {
		int ch = -1;
		
		while ((ch = get_ch()) != -1 && Character.isWhitespace(ch)) { }
		ScanLocation scan_loc = getLocation();
	
		String type;
		if (ch == -1) {
			type = "";
		} else {
			type = readPreProcIdentifier(ch);
	
			if (type == null) {
				type = "";
			}
		}
		
		if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
		
			// TODO: line number tracking
			ch = skipWhite(get_ch());
			
			// TODO: evaluate the expression?
			String remainder = readPreProcIdentifier(ch);
			
			if (remainder != null) {
				remainder = remainder.trim();
			} else {
				remainder = "";
			}
		
			// Add a new entry to the referenced macros 
			add_macro_reference(remainder);

			if (type.equals("ifdef")) {
				if (fDebugEn) {
					fLog.debug("ifdef \"" + remainder + "\": " +
							fDefineProvider.isDefined(remainder, -1));
				}
				boolean active = fDefineProvider.isDefined(remainder, -1);
				enter_ifdef(scan_loc, active);
			} else if (type.equals("ifndef")) {
				boolean active = !fDefineProvider.isDefined(remainder, -1);
				if (fDebugEn) {
					fLog.debug("ifndef \"" + remainder + "\": " + active);
				}
				enter_ifdef(scan_loc, active);
			} else { // elsif
				boolean active = fDefineProvider.isDefined(remainder, -1);
				
				enter_elsif(scan_loc, active);
			}
		} else if (type.equals("else")) {
			enter_else(scan_loc);
		} else if (type.equals("endif")) {
			leave_ifdef(scan_loc);
		} else if (fIgnoredDirectives.contains(type)) {
			// Skip entire line 
			readLine(get_ch());
		} else if (type.equals("define")) {
			SVDBLocation location = new SVDBLocation(
				scan_loc.getFileId(), scan_loc.getLineNo(), scan_loc.getLinePos());
			SVDBMacroDef m = new SVDBMacroDef();
			// TODO: save file?

			// TODO: line numbers
			ch = skipWhite(get_ch());
			
			m.setName(readIdentifier(ch));
			m.setLocation(location);
			
			fParamList.clear();
			
			ch = get_ch();
			
			if (ch == '(') {
				// Has parameters
				List<SVDBMacroDefParam> param_list = new ArrayList<SVDBMacroDefParam>();
				
				do {
					ch = skipWhite(get_ch());
					
					if (!(Character.isJavaIdentifierPart(ch))) {
						break;
					} else {
						String p = readIdentifier(ch);
						String dflt = null;

						ch = skipWhite(get_ch());

						if (ch == '=') {
							// Read default value
							ch = skipWhite(get_ch());
							if (ch == '"') {
								// String
								dflt = readString(ch);
								dflt = "\"" + dflt + "\"";
							} else {
								// Read up to comma or close bracket
								startCapture(ch);
								while ((ch = get_ch()) != -1 && ch != ',' && ch != ')') { }
								unget_ch(ch);
								dflt = endCapture();
							}
						} else {
							unget_ch(ch);
						}
						
						param_list.add(new SVDBMacroDefParam(p, dflt));
					}
					
					ch = skipWhite(get_ch());
				} while (ch == ',');
				
				m.setParameters(param_list);
				
				if (ch == ')') {
					ch = get_ch();
				}
				
			}

			// Now, read the remainder of the definition
			String define = readLine(ch);
			
			
			if (define == null) {
				define = ""; // define this macro as existing
			}

			/* We should carry-through the single-line comments. However, this is only
			 * true in the case of a single-line macro. Multi-line macros get to keep
			 * their single-line comments
			 */ 
			int last_comment;
			if ((last_comment = define.lastIndexOf("//")) != -1) {
				int lr = define.indexOf('\n', last_comment);
				if (lr == -1) {
					// Nothing beyond this comment
					define = define.substring(0, define.indexOf("//"));
				}
			}
			
			m.setDef(define);
		
			// TODO: need to warn on re-definition?
			if (ifdef_enabled()) {
				addMacro(m);
				
				SVPreProc2InputData in = currentRealFile();
				
				// Add the macro to the pre-processor version of the file
				if (in != null && in.getFileTree() != null && in.getFileTree().getSVDBFile() != null) {
					in.getFileTree().getSVDBFile().addChildItem(m);
					in.getFileTree().addToMacroSet(m);
				}
			}
		} else if (type.equals("include")) {
			ch = skipWhite(get_ch());
			
			if (ch == '"') {
				String inc = readString(ch);

				if (inc.length() > 2 && ifdef_enabled()) {
					// TODO: need to save the include statement in the pre-proc view?
					
					// Process include and switch to new file
					if (fIncFileProvider != null) {
						Tuple<String, List<SVDBFileTreeMacroList>> defs;
						Tuple<String, InputStream> in;
					
						// TODO: for now, assuming accumulated pre-processor state 
						// doesn't change file content. This isn't precisely correct.
						defs = fIncFileProvider.findCachedIncFile(inc);
						
						SVPreProc2InputData curr_in = fInputCurr;
						if (defs != null) {
							// Add in the macros from the included file
							for (SVDBFileTreeMacroList l : defs.second()) {
								for (SVDBMacroDef m : l.getMacroList()) {
									addMacro(m);
								}
							}
						
							// TODO: Need to mark as a 'virtual' include?
							SVDBInclude svdb_inc = new SVDBInclude(inc);
							svdb_inc.setLocation(new SVDBLocation(
									scan_loc.getFileId(), 
									scan_loc.getLineNo(),
									scan_loc.getLinePos()));
							
							curr_in.getFileTree().getSVDBFile().addChildItem(svdb_inc);
							
							SVDBFileTree ft_i = new SVDBFileTree(defs.first());
							ft_i.setParent(curr_in.getFileTree());
							curr_in.getFileTree().addIncludedFileTree(ft_i);
					
							for (SVDBFileTreeMacroList ml : defs.second()) {
								for (SVDBMacroDef m : ml.getMacroList()) {
									ft_i.addToMacroSet(m);
								}
							}
						} else if ((in = fIncFileProvider.findIncFile(inc)) != null && in.second() != null) {
							if (fDebugEn) {
								fLog.debug("Switching from file " + 
										curr_in.getFileName() + " to " + in.first());
							}
							
							// TODO: Add tracking data for new file
							
							// Believe it or not, some recursive inclusion is functional...
							int recursive_include_count = 0;
							
							if (fFileList.contains(in.first())) {
								for (int i=0; i<fInputStack.size(); i++) {
									if (fInputStack.get(i).getFileName().equals(in.first())) {
										recursive_include_count++;
									}
								}
							}
							
							if (recursive_include_count < 10) {
								// Find the root file path
								String rootfile = fInputStack.get(0).getFileName();
								fIncFileProvider.addCachedIncFile(in.first(), rootfile);

								SVDBInclude svdb_inc = new SVDBInclude(inc);
								svdb_inc.setLocation(new SVDBLocation(
										scan_loc.getFileId(), 
										scan_loc.getLineNo(),
										scan_loc.getLinePos()));

								curr_in.getFileTree().getSVDBFile().addChildItem(svdb_inc);

								enter_file(in.first(), in.second());
							} else {
								// Recursive include and have exceeded the limit
								SVDBLocation location = new SVDBLocation(
										scan_loc.getFileId(), scan_loc.getLineNo(), 
										scan_loc.getLinePos());
								
								SVDBMarker m = new SVDBMarker(MarkerType.Error, 
										MarkerKind.MissingInclude,
										"Recursive inclusion of file " + inc);
								m.setLocation(location);
								curr_in.getFileTree().fMarkers.add(m);
								try {
									in.second().close();
								} catch (IOException e) {}
							}
						} else {
							SVDBLocation location = new SVDBLocation(
									scan_loc.getFileId(), scan_loc.getLineNo(), 
									scan_loc.getLinePos());
							
							SVDBMarker m = new SVDBMarker(MarkerType.Error, 
									MarkerKind.MissingInclude,
									"Failed to find include file " + inc);
							m.setLocation(location);
//							SVPreProc2InputData curr_in = fInputCurr;
							curr_in.getFileTree().fMarkers.add(m);

							// TODO: add missing-include error
							if (fDebugEn) {
								fLog.debug("Failed to find include file " + inc);
							}
						}
					}
				} else {
					inc = "";
				}
			}
		} else if (type.equals("__LINE__")) {
			if (ifdef_enabled()) {
				output("" + fInputCurr.getLineNo());
			}
		} else if (type.equals("__FILE__")) {
			if (ifdef_enabled()) {
				output("\"" + fInputCurr.getFileName() + "\"");
			}
		} else if (type.equals("pragma")) {
			ch = skipWhite(get_ch());
			String id = readIdentifier(ch);
			
			if (id != null) {
				// Ignore everything in the 'protected' region. 
				// Not much we can meaningfully show...
				if (id.equals("protect")) {
					ch = skipWhite(get_ch());
					
					id = readIdentifier(ch);
					
					if (id != null) {
						if (id.equals("begin_protected")) {
							enter_ifdef(scan_loc, false);
						} else if (id.equals("end_protected")) {
							leave_ifdef(scan_loc);
						}
					}
				}
			}
		} else if (type.equals("protected")) {
			enter_ifdef(scan_loc, false);
		} else if (type.equals("endprotected")) {
			leave_ifdef(scan_loc);
		} else if (!type.equals("")) {
			// Note: type="" occurs when no identifier followed the tick
			// macro expansion.
			// TODO: is TmpBuffer available?
			fTmpBuffer.setLength(0);
			
			fTmpBuffer.append('`');
			fTmpBuffer.append(type);

			// If we're in a disabled section, don't try to expand
			if (ifdef_enabled()) {
				// Read the full string
			
				// Add a reference for this macro
				add_macro_reference(type);

				boolean is_defined = fDefineProvider.isDefined(type, -1);
				if (!is_defined) {
					SVDBLocation location = new SVDBLocation(
							scan_loc.getFileId(), scan_loc.getLineNo(), 
							scan_loc.getLinePos());
					
					SVDBMarker m = new SVDBMarker(MarkerType.Error, 
							MarkerKind.UndefinedMacro,
							"Macro " + type + " undefined");
					m.setLocation(location);

					fInputCurr.getFileTree().fMarkers.add(m);

				}
				
				if (fDefineProvider.hasParameters(type, fInputCurr.getLineNo()) || !is_defined) {
					// Try to read the parameter list
					ch = get_ch();
					// skip up to new-line or non-whitespace
					if (!is_defined) {
						// For undefined macros, only search up to end-of-line
						while (ch != -1 && Character.isWhitespace(ch) && ch != '\n') {
							ch = get_ch();
						}
					} else {
						// For defined macros, skip all whitespace
						while (ch != -1 && Character.isWhitespace(ch)) {
							ch = get_ch();
						}
					}

					if (ch == '(') {
						fTmpBuffer.append((char)ch);

						// Read the parameter list
						int matchLevel=1, last_ch = -1;
						boolean in_string = false;

						do {
							ch = get_ch();

							if (!in_string) {
								if (ch == '(') {
									matchLevel++;
								} else if (ch == ')') {
									matchLevel--;
								} else if (ch == '\"' && last_ch != '\\') {
									in_string = true;
								}
							} else if (ch == '\"' && last_ch != '\\') {
								in_string = false;
							}

							if (ch != -1) {
								fTmpBuffer.append((char)ch);
							}
						} while (ch != -1 && matchLevel > 0);
					} else if (is_defined) {
						unget_ch(ch);
					} else {
						unget_ch(ch);
					}
				}

				if (!is_defined) {
					// Leave a breadcrumb for the lexer
					output("`undefined");
				} else if (fDefineProvider != null) {
					try {
						String exp = fDefineProvider.expandMacro(
								fTmpBuffer.toString(), fInputCurr.getFileName(), fInputCurr.getLineNo());

						if (fDebugEn) {
							fLog.debug("Expansion of \"" + 
									fTmpBuffer.toString() + "\" == " + exp);
						}

						SVPreProc2InputData in = new SVPreProc2InputData(
								this, new StringInputStream(exp), 
								"ANONYMOUS", fInputCurr.getFileId(), false);
						fInputStack.push(in);
						fInputCurr = in;
					} catch (Exception e) {
						/*
							System.out.println("Exception while expanding \"" + 
									fTmpBuffer.toString() + "\" @ " +
									getLocation().getFileName() + ":" + 
									getLocation().getLineNo());
						 */
						e.printStackTrace();
					}
				}
			}
			
		}
	}
	
	private void enter_file(String filename, InputStream in) {
		if (!fFileList.contains(filename)) {
			fFileList.add(filename);
		} else {
//			System.out.println("File: " + filename + " already included");
		}
		
		
		// Add a marker noting that we're switching to a new file
		int file_id = 0;
		
		if (fFileMapper != null) {
			file_id = fFileMapper.mapFilePathToId(filename, true);
		}
		
		SVFileBuffer in_b = new SVFileBuffer(in);
		SVPreProc2InputData in_data = new SVPreProc2InputData(this, in_b, filename, file_id);
		add_file_change_info(file_id, in_data.getLineNo());

		
		in_data.setFileTree(new SVDBFileTree(new SVDBFile(filename)));
		
		// Record the current state of the pre-processor
//		in_data.fFileTree.fMacroEntryState.putAll(fMacroMap);
	
		if (!fInputStack.empty()) {
			SVPreProc2InputData p_data = fInputCurr;
			in_data.getFileTree().setParent(p_data.getFileTree());
			p_data.getFileTree().addIncludedFileTree(in_data.getFileTree());
		}

		fInputStack.push(in_data);
		fInputCurr = in_data;
	}
	
	private void cleanup_preproc_leftovers() {
		int file_id = fInputCurr.getFileId();
		while (fPreProcLoc.size() > 0 && fPreProcLoc.peek().getFileId() == file_id) {
			
			// Leftovers indicates unbalanced directives
			ScanLocation loc = fPreProcLoc.pop();
			fPreProcEn.pop();
			SVDBLocation location = new SVDBLocation(loc.getFileId(), 
					loc.getLineNo(), loc.getLinePos());
			SVDBMarker m = new SVDBMarker(MarkerType.Error, 
					MarkerKind.UnbalancedDirective, 
					"Unbalanced pre-processor directive");
			
			if (fDebugEn) {
				fLog.debug("Cleanup pre-proc leftover @ " + loc.getLineNo());
			}
			m.setLocation(location);
			if (fInputCurr.getFileTree() != null) {
				fInputCurr.getFileTree().fMarkers.add(m);
			}
		}		
	}
	
	private void leave_file() {
		SVPreProc2InputData old_file = fInputCurr;

		
		// Clean up (if needed) after the macro stack
		// Only cleanup after leaving a file where file content (not expanded macro content)
		// was present
		if (fInputCurr.incPos()) {
			cleanup_preproc_leftovers();
		}
		
		fInputCurr.leave_file();
		
		if (fIndexStats != null) {
			// Update stats
			if (old_file.getInput() instanceof SVFileBuffer) {
				fIndexStats.incLastIndexFileReadTime(
						((SVFileBuffer)old_file.getInput()).getReadTime());
			}
			fIndexStats.incNumLines(old_file.getLineCount());
			fIndexStats.incNumProcessedFiles();
		}
		
		/*SVPreProc2InputData curr_in =*/ fInputStack.pop();
		
		SVPreProc2InputData new_file = fInputStack.peek();
		fInputCurr = new_file;
		
		int file_idx = fFileList.indexOf(new_file.getFileName());

		// We will not have registered ANONYMOUS files
		if (file_idx != -1) {
			int file_id = 0;
			
			if (fFileMapper != null) {
				file_id = fFileMapper.mapFilePathToId(new_file.getFileName(), true);
			}
			
			// Add a marker noting that we're switching to a new file
			SVPreProcOutput.FileChangeInfo file_info =
					new SVPreProcOutput.FileChangeInfo(
							fOutputLen, file_id, new_file.getLineNo());
			fFileMap.add(file_info);
		}
	}
	
	private void add_macro_reference(String macro) {
		SVPreProc2InputData in = fInputCurr;
		SVDBMacroDef def = fMacroProvider.findMacro(macro, -1);

		in.addReferencedMacro(macro, def);
	}
	
	private void enter_ifdef(ScanLocation scan_loc, boolean enabled) {
		boolean enabled_pre = ifdef_enabled();
		int e = (enabled)?PP_ENABLED:PP_DISABLED;
		
		if (fPreProcEn.size() > 0) {
			int e_t = fPreProcEn.peek();
			
			if ((e_t & PP_ENABLED) == 0) {
				// Anything beneath a disabled section is also disabled
				e = PP_DISABLED;
				e |= PP_CARRY;
			}
		}
		
		// Mark that we've taken one branch
		if ((e & PP_ENABLED) == 1) {
			e |= PP_THIS_LEVEL_EN_BLOCK;
		}
		
		fPreProcEn.push(e);
		fPreProcLoc.push(scan_loc);
	
		if (fDebugEn) {
			fLog.debug("enter_ifdef: " + scan_loc.getLineNo() + 
					" enabled=" + enabled + " pre=" + enabled_pre + 
					" post=" + ifdef_enabled() + " sz=" + fPreProcEn.size());
		}
		
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void leave_ifdef(ScanLocation scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			fPreProcEn.pop();
			fPreProcLoc.pop();
		}
	
		if (fDebugEn) {
			fLog.debug("leave_ifdef: " + scan_loc.getLineNo() + 
					" pre=" + enabled_pre + 
					" post=" + ifdef_enabled());
		}
		
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_elsif(ScanLocation scan_loc, boolean enabled) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();
			fPreProcLoc.pop();

			if (enabled) {
				// Condition evaluates true
				if ((e & PP_CARRY) != PP_CARRY && 
						(e & PP_THIS_LEVEL_EN_BLOCK) != PP_THIS_LEVEL_EN_BLOCK) {
					// Enable this branch
					e |= (PP_ENABLED | PP_THIS_LEVEL_EN_BLOCK);
				}
			} else {
				// Not enabled. Ensure the ENABLED flag is cleared
				e &= ~PP_ENABLED;
			}
			
			fPreProcEn.push(e);
			fPreProcLoc.push(scan_loc);
		}
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_else(ScanLocation scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();
			fPreProcLoc.pop();
			
			// Invert only if we're in an enabled scope and
			// we haven't already 'taken' a branch in the 
			// ifdef/elsif/else structure
			if ((e & PP_CARRY) == 0) {
				
				if ((e & PP_THIS_LEVEL_EN_BLOCK) != 0) {
					// Disable any blocks beyond the 'taken' block
					e &= ~PP_ENABLED;
				} else {
					// Enable this branch and set the BLOCK_ENABLED flag
					e |= PP_ENABLED;
				}
			}
			
			// Flip to 'true' only if we aren't 
			fPreProcEn.push(e);
			fPreProcLoc.push(scan_loc);
		} else {
			fLog.debug("Warning: encountered `else with empty PreProcEn stack");
		}
		
		if (fDebugEn) {
			fLog.debug("enter_else: " + scan_loc.getLineNo() + 
					" pre=" + enabled_pre + 
					" post=" + ifdef_enabled());
		}
		
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private boolean ifdef_enabled() {
		
		if (fPreProcEn.size() == 0) {
			return true;
		} else {
			int e = fPreProcEn.peek();
			return ((e & PP_ENABLED) == PP_ENABLED);
		}
	}	
	
	private void update_unprocessed_region(ScanLocation scan_loc, boolean enabled_pre) {
		boolean enabled_post = ifdef_enabled();
		
		// TODO: need to identify exclusions due to multiple includes?
		// eg:
		// `ifndef FILE_INCLUDED
		// `define FILE_INCLUDED
		// 
		// `endif
		
		fInputCurr.update_unprocessed_region(scan_loc, enabled_pre, enabled_post);
	}
	
	private String readLine(int ci) {
		int last_ch = -1;
		
		fTmpBuffer.setLength(0);
		while (ci != -1 && ci != '\n' || last_ch == '\\') {
			if (last_ch == '\\' && ci == '\n') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
					fTmpBuffer.setLength(fTmpBuffer.length()-1);
				}
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, '\n');
				}
			} else {
				fTmpBuffer.append((char)ci);
			}

			if (ci != '\r') {
				last_ch = ci;
			}

			ci = get_ch();
		}
		
		unget_ch(ci);

		if (fTmpBuffer.length() == 0) {
			return null;
		} else {
			return fTmpBuffer.toString();
		}
	}	
	
	public int get_ch() {
		int ch = fInputCurr.get_ch();
		
		if (ch == -1) {
			while (fInputStack.size() > 0) {
				SVPreProc2InputData in = fInputStack.peek();

				ch = in.get_ch();

				if (ch == -1 && fInputStack.size() > 1) {
					leave_file();
					continue;
				} else {
					// Always leave one on the stack
					break;
				}
			}
		} 
	
		return ch;
	}
	
	public void unget_ch(int ch) {
		fInputCurr.unget_ch(ch);

		/*
		if (ch != -1 && fCaptureEnabled && fCaptureBuffer.length() > 0) {
			fCaptureBuffer.deleteCharAt(fCaptureBuffer.length()-1);
		}
		 */
	}
	
	private void output(int ch) {
		fOutput.append((char)ch);
		fOutputLen++;
	}
	
	private void output(String str) {
		fOutput.append(str);
		fOutputLen = fOutput.length();
	}

	/*
	public void preProcError(String msg, String filename, int lineno) {
		SVDBMarker m = new SVDBMarker(
				MarkerType.Error, MarkerKind.UndefinedMacro, msg);
//		m.setLocation(new SVDBLocation(line, pos))
		
	} 
	 */
	
	public SVDBMacroDef findMacro(String name, int lineno) {
		return fMacroProvider.findMacro(name, lineno);
	}
	
	public void addMacro(SVDBMacroDef macro) {
		if (ifdef_enabled()) {
			fMacroProvider.addMacro(macro);
		}
	}
	
	public void setMacro(SVDBMacroDef macro) {
		fMacroProvider.addMacro(macro);
	}

	public void setMacro(String key, String value) {
		fMacroProvider.setMacro(key, value);
	}
	
	public ScanLocation getLocation() {
		return fInputCurr.getLocation();
	}

	/**
	 * Unused
	 */
	public long getPos() {
		return -1;
	}
	
	void add_file_change_info(int file_id, int lineno) {
		int pos = fOutputLen;
		int ex_file_id = -1;
		int ex_lineno = -1;
		int ex_pos = -1;
		
		if (fFileMap.size() > 0) {
			ex_file_id = fFileMap.get(fFileMap.size()-1).fFileId;
			ex_lineno  = fFileMap.get(fFileMap.size()-1).fLineno;
			ex_pos     = fFileMap.get(fFileMap.size()-1).fStartIdx;
		}
		
		if (pos != ex_pos || file_id != ex_file_id || lineno != ex_lineno) {
			SVPreProcOutput.FileChangeInfo file_info = new SVPreProcOutput.FileChangeInfo(
					pos, file_id, lineno);
			fFileMap.add(file_info);		
		}
	}
	
	private IPreProcMacroProvider defaultMacroProvider = new IPreProcMacroProvider() {
		
		public void setMacro(String key, String value) {
			if (value == null) {
				fMacroMap.remove(value);
			} else {
				addMacro(new SVDBMacroDef(key, value));
			}
		}
		
		public SVDBMacroDef findMacro(String name, int lineno) {
			SVDBMacroDef m = fMacroMap.get(name);
			// SVPreProc2InputData in = fInputCurr;
			
			// TODO: Add macro reference to current file data
			fInputCurr.addRefMacro(name, m);

			
			return m;			
		}
		
		public void addMacro(SVDBMacroDef macro) {
			if (fMacroMap.containsKey(macro.getName())) {
				fMacroMap.remove(macro.getName());
			}
			fMacroMap.put(macro.getName(), macro);
		}
	};

	@Override
	public void preProcError(String msg, String filename, int lineno) {
		// TODO Auto-generated method stub
		
	}
	
}
