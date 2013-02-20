package net.sf.sveditor.core.preproc;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBUnprocessedRegion;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanner.SVPreProcDefineProvider;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcessor2 extends AbstractTextScanner implements IPreProcMacroProvider {
	private Map<String, SVDBMacroDef>				fMacroMap;
	private ISVPreProcIncFileProvider				fIncFileProvider;
	private String									fFileName;
	private StringBuilder							fOutput;
	private StringBuilder							fCommentBuffer;
	private boolean									fInComment;
	private IDocCommentParser   					fDocCommentParser;
	private ScanLocation							fCommentStart;							
	private List<Integer>							fLineMap;

	// List of offset,file-id pairs
	private List<SVPreProcOutput.FileChangeInfo>	fFileMap;
	private List<String>							fFileList;
	private StringBuilder							fTmpBuffer;
	private List<Tuple<String, String>>				fParamList;
	private Stack<Integer>							fPreProcEn;
	private SVPreProcDefineProvider					fDefineProvider;
	private boolean									fInPreProcess;
	private LogHandle								fLog;
	private List<SVDBMarker>						fMarkers;
	private boolean									fDebugEn = true;
	
	private Stack<InputData>						fInputStack;
	private ISVPreProcFileMapper					fFileMapper;
	
	private static class InputData {
		InputStream				fInput;
		String					fFilename;
		int						fFileId;
		int						fLineno;
		int						fLinepos;
		byte					fInBuffer[];
		int						fInBufferIdx;
		int						fInBufferMax;
		int						fLastCh;
		int						fUngetCh[] = {-1,-1};
		boolean					fEof;
		// Macros referenced by this file
		Map<String, String>		fRefMacros;
		SVDBFileTree			fFileTree;
		SVDBUnprocessedRegion	fUnprocessedRegion;
		
		InputData(InputStream in, String filename, int file_id) {
			fLineno = 1;
			fInput = in;
			fFilename = filename;
			fFileId   = file_id;
			fInBuffer = new byte[4*1024];
			fInBufferIdx = 0;
			fInBufferMax = 0;
			fLastCh = -1;
			fEof = false;
			fRefMacros = new HashMap<String, String>();
		}
	}
	
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
		fIgnoredDirectives.add("timescale");
		// Ignored for now
		fIgnoredDirectives.add("resetall");
		fIgnoredDirectives.add("unconnected_drive");
		// Ignored for now
		fIgnoredDirectives.add("undef");
		fIgnoredDirectives.add("undefineall");
	}

	public SVPreProcessor2(
			String							filename,
			InputStream	 					input, 
			ISVPreProcIncFileProvider		inc_provider,
			ISVPreProcFileMapper			file_mapper) {
		fMacroMap = new HashMap<String, SVDBMacroDef>();
		fInputStack = new Stack<SVPreProcessor2.InputData>();
		fOutput = new StringBuilder();
		fCommentBuffer = new StringBuilder();
		fDocCommentParser = new DocCommentParser();
		fTmpBuffer = new StringBuilder();
		fParamList = new ArrayList<Tuple<String,String>>();
		fPreProcEn = new Stack<Integer>();
		fLineMap = new ArrayList<Integer>();
		fFileMap = new ArrayList<SVPreProcOutput.FileChangeInfo>();
		fFileList = new ArrayList<String>();

		fFileName = filename;
		fIncFileProvider 	= inc_provider;
		fFileMapper			= file_mapper;
		
		fDefineProvider = new SVPreProcDefineProvider(this);
		
		fLog = LogFactory.getLogHandle("SVPreProcessor2");
	
		// Add the first file
		enter_file(filename, input);
	}
	
	public SVPreProcOutput preprocess(List<SVDBMarker> markers) {
		int ch, last_ch = -1;
		int end_comment[] = {-1, -1};
		boolean in_string = false;
		boolean ifdef_enabled = true;
		boolean found_single_line_comment = false;
		
		fInPreProcess = true;
		fMarkers = markers;

		while ((ch = get_ch()) != -1) {
			found_single_line_comment = false;
			if (!in_string) {
				// Handle comment
				if (ch == '/') {
					int ch2 = get_ch();

					if (ch2 == '/') {
						fOutput.append(' '); // ch
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
						end_comment[0] = -1;
						end_comment[1] = -1;

						fOutput.append(' '); // ch

						beginComment();
						while ((ch = get_ch()) != -1) {
							end_comment[0] = end_comment[1];
							end_comment[1] = ch;

							if (end_comment[0] == '*' && end_comment[1] == '/') {
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
						fOutput.append(' ');
					}
				} else {
					if (ch == '"' && last_ch != '\\') {
						// Enter string
						in_string = true;
					}
					if (ifdef_enabled) {
						fOutput.append((char)ch);
					}
				}
			} else {
				// In String
				if (ch == '"' && last_ch != '\\') {
					in_string = false;
				}
				if (ifdef_enabled) {
					fOutput.append((char)ch);
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
		
		fInPreProcess = false;
		
		
		SVPreProcOutput ret = new SVPreProcOutput(
				fOutput, fLineMap, fFileMap, fFileList);
		ret.setFileTree(fInputStack.peek().fFileTree);
		
		return ret;
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
			InputData in = fInputStack.peek();
			SVDBDocComment doc_comment = new SVDBDocComment(title, comment);
			SVDBLocation loc = new SVDBLocation(fCommentStart.getFileId(),  
					fCommentStart.getLineNo(), fCommentStart.getLinePos());
			doc_comment.setLocation(loc);
			in.fFileTree.getSVDBFile().addChildItem(doc_comment);
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
			type = readIdentifier(ch);
	
			if (type == null) {
				type = "";
			}
		}
		
		if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
		
			// TODO: line number tracking
			ch = skipWhite(get_ch());
			
			// TODO: evaluate the expression?
			String remainder = readIdentifier(ch);
			
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
							fDefineProvider.isDefined(remainder, fLineno));
				}
				boolean active = fDefineProvider.isDefined(remainder, fLineno);
				enter_ifdef(scan_loc, active);
			} else if (type.equals("ifndef")) {
				boolean active = !fDefineProvider.isDefined(remainder, fLineno);
				if (fDebugEn) {
					fLog.debug("ifndef \"" + remainder + "\": " + active);
				}
				enter_ifdef(scan_loc, active);
			} else { // elsif
				boolean active = fDefineProvider.isDefined(remainder, fLineno);
				
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
				
				InputData in = fInputStack.peek();
				// Add the macro to the pre-processor version of the file
				in.fFileTree.getSVDBFile().addChildItem(m);
			}
		} else if (type.equals("include")) {
			ch = skipWhite(get_ch());
			
			if (ch == '"') {
				String inc = readString(ch);

				if (inc.length() > 2) {
					// TODO: need to save the include statement in the pre-proc view?
					
					// Process include and switch to new file
					if (fIncFileProvider != null) {
						Tuple<String, InputStream> in = fIncFileProvider.findIncFile(inc);
						
						if (in != null) {
							if (fDebugEn) {
								InputData curr_in = fInputStack.peek();
								fLog.debug("Switching from file " + 
										curr_in.fFilename + " to " + in.first());
							}
							// TODO: Add tracking data for new file
							
							enter_file(in.first(), in.second());
						} else {
							SVDBLocation location = new SVDBLocation(
									scan_loc.getFileId(), scan_loc.getLineNo(), 
									scan_loc.getLinePos());
							
							SVDBMarker m = new SVDBMarker(MarkerType.Error, 
									MarkerKind.MissingInclude,
									"Failed to find include file " + inc);
							m.setLocation(location);
							if (fMarkers != null) {
								fMarkers.add(m);
							}

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
			fOutput.append("" + fLineno);
		} else if (type.equals("__FILE__")) {
			fOutput.append("\"" + fFileName + "\"");
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

				boolean is_defined = fDefineProvider.isDefined(type, fLineno);
				if (!is_defined) {
					SVDBLocation location = new SVDBLocation(
							scan_loc.getFileId(), scan_loc.getLineNo(), 
							scan_loc.getLinePos());
					
					SVDBMarker m = new SVDBMarker(MarkerType.Error, 
							MarkerKind.UndefinedMacro,
							"Macro " + type + " undefined");
					m.setLocation(location);
					
					if (fMarkers != null) {
						fMarkers.add(m);
					}
				}
				
				if (fDefineProvider.hasParameters(type, fLineno) || !is_defined) {
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

				if (fDefineProvider != null) {
						try {
							String exp = fDefineProvider.expandMacro(
											fTmpBuffer.toString(), fFileName, fLineno);
							if (fDebugEn) {
								fLog.debug("Expansion of \"" + 
										fTmpBuffer.toString() + "\" == " + exp);
							}
							InputData in = new InputData(new StringInputStream(exp), "ANONYMOUS", -1);
							fInputStack.push(in);
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
		}
		
		// Add a marker noting that we're switching to a new file
		int file_id = 0;
		
		if (fFileMapper != null) {
			file_id = fFileMapper.mapFilePathToId(filename, true);
		}
		InputData in_data = new InputData(in, filename, file_id);
		SVPreProcOutput.FileChangeInfo file_info = 
				new SVPreProcOutput.FileChangeInfo(
						fOutput.length(), file_id, in_data.fLineno);
		fFileMap.add(file_info);
		
		in_data.fFileTree = new SVDBFileTree(new SVDBFile(filename));
	
		if (!fInputStack.empty()) {
			InputData p_data = fInputStack.peek();
			in_data.fFileTree.setParent(p_data.fFileTree);
			p_data.fFileTree.fIncludedFileTrees.add(in_data.fFileTree);
		}

		fInputStack.push(in_data);
	}
	
	private void leave_file() {
		InputData old_file = fInputStack.peek();
		
		if (old_file.fUnprocessedRegion != null) {
			// TODO: mark error
			// we fell off the end of the file with an ifdef active
			ScanLocation scan_loc = getLocation();
			SVDBLocation loc = new SVDBLocation(scan_loc.getFileId(), 
					scan_loc.getLineNo(), scan_loc.getLinePos());
			old_file.fUnprocessedRegion.setEndLocation(loc);
			old_file.fFileTree.getSVDBFile().addChildItem(old_file.fUnprocessedRegion);
		}
		
		fInputStack.pop();
		
		// TODO: 

		InputData new_file = fInputStack.peek();
		
		int file_idx = fFileList.indexOf(new_file.fFilename);

		// We will not have registered ANONYMOUS files
		if (file_idx != -1) {
			int file_id = 0;
			
			if (fFileMapper != null) {
				file_id = fFileMapper.mapFilePathToId(new_file.fFilename, true);
			}
			
			// Add a marker noting that we're switching to a new file
			SVPreProcOutput.FileChangeInfo file_info =
					new SVPreProcOutput.FileChangeInfo(
							fOutput.length(), file_id, new_file.fLineno);
			fFileMap.add(file_info);
		}
	}
	
	private void add_macro_reference(String macro) {
		InputData in = fInputStack.peek();
		in.fFileTree.fReferencedMacros.remove(macro);
		SVDBMacroDef def = fMacroMap.get(macro);
		
		if (def == null) {
			in.fFileTree.fReferencedMacros.put(macro, null);
		} else {
			in.fFileTree.fReferencedMacros.put(macro, def.getDef());
		}		
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
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void leave_ifdef(ScanLocation scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			fPreProcEn.pop();
		}
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_elsif(ScanLocation scan_loc, boolean enabled) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();

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
		}
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_else(ScanLocation scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			int e = fPreProcEn.pop();
			
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
		InputData in = fInputStack.peek();
		
		// TODO: need to identify exclusions due to multiple includes?
		// eg:
		// `ifndef FILE_INCLUDED
		// `define FILE_INCLUDED
		// 
		// `endif

		if (enabled_pre && !enabled_post) {
			// Entering an unprocessed region
			SVDBLocation loc = new SVDBLocation(scan_loc.getFileId(), 
					scan_loc.getLineNo(), scan_loc.getLinePos());
		
			in.fUnprocessedRegion = new SVDBUnprocessedRegion();
			in.fUnprocessedRegion.setLocation(loc);
		} else if (!enabled_pre && enabled_post) {
			// Leaving an unprocessed region
			SVDBLocation loc = new SVDBLocation(scan_loc.getFileId(), 
					scan_loc.getLineNo(), scan_loc.getLinePos());
		
			SVDBUnprocessedRegion r = in.fUnprocessedRegion;
			in.fUnprocessedRegion = null;
			
			r.setEndLocation(loc);
			in.fFileTree.getSVDBFile().addChildItem(r);
		}
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
		int ch = -1;
		
		if (!fInPreProcess) {
			throw new RuntimeException("Cannot call SVPreProcessor.get_ch() outside preprocess()");
		}
		
		while (fInputStack.size() > 0) {
			InputData in = fInputStack.peek();
			fLineno = in.fLineno;
			fFileName = in.fFilename;
		
			if (in.fUngetCh[0] != -1) {
				ch = in.fUngetCh[0];
				in.fUngetCh[0] = in.fUngetCh[1];
				in.fUngetCh[1] = -1;
				break;
			} else if (in.fEof) {
				// TODO: Signal move back to previous 
				if (fInputStack.size() > 1) {
					leave_file();
					continue;
				} else {
					// Always leave one on the stack
					break;
				}
			} else {
				if (in.fInBufferIdx >= in.fInBufferMax) {
					// Time to read more data
					try {
						in.fInBufferMax = in.fInput.read(
								in.fInBuffer, 0, in.fInBuffer.length);
						in.fInBufferIdx = 0;
						if (in.fInBufferMax <= 0) {
							in.fInput.close();
							if (fDebugEn) {
								fLog.debug("Reached the end of file " +
										in.fFilename);
							}
							in.fEof = true;
						}
					} catch (IOException e) {}
				}
				if (in.fInBufferIdx < in.fInBufferMax) {
					ch = in.fInBuffer[in.fInBufferIdx++];
					if (in.fLastCh == '\n') {
						// Save a marker for the line in the line-map
						fLineMap.add(fOutput.length()-1);
						in.fLineno++;
						fLineno = in.fLineno;
					}
					in.fLastCh = ch;
					break;
				} else {
					// Reached end of the file...
					// fInputStack.pop();
				}
			}
		}	

		if (ch != -1 && fCaptureEnabled) {
			fCaptureBuffer.append((char)ch);
		}

		return ch;
	}
	
	public void unget_ch(int ch) {
		InputData in = fInputStack.peek();
		if (in.fUngetCh[0] == -1) {
			in.fUngetCh[0] = ch;
		} else {
			in.fUngetCh[1] = in.fUngetCh[0];
			in.fUngetCh[0] = ch;
		}

		if (ch != -1 && fCaptureEnabled && fCaptureBuffer.length() > 0) {
			fCaptureBuffer.deleteCharAt(fCaptureBuffer.length()-1);
		}
	}

	/*
	public void preProcError(String msg, String filename, int lineno) {
		SVDBMarker m = new SVDBMarker(
				MarkerType.Error, MarkerKind.UndefinedMacro, msg);
//		m.setLocation(new SVDBLocation(line, pos))
		
	} 
	 */
	
	public SVDBMacroDef findMacro(String name, int lineno) {
		SVDBMacroDef m = fMacroMap.get(name);
		InputData in = fInputStack.peek();
		
		// TODO: Add macro reference to current file data
		in.fRefMacros.remove(name);
		if (m == null) {
			in.fRefMacros.put(name, null);
		} else {
			in.fRefMacros.put(name, m.getDef());
		}
		
		return m;
	}

	public void addMacro(SVDBMacroDef macro) {
		if (ifdef_enabled()) {
			if (fMacroMap.containsKey(macro.getName())) {
				fMacroMap.remove(macro.getName());
			}
			fMacroMap.put(macro.getName(), macro);
		}
	}

	public void setMacro(String key, String value) {
		addMacro(new SVDBMacroDef(key, value));
	}

	public ScanLocation getLocation() {
		InputData in = fInputStack.peek();
		return new ScanLocation(in.fFileId, in.fLineno, in.fLinepos);
	}

	/**
	 * Unused
	 */
	public long getPos() {
		return -1;
	}
}
