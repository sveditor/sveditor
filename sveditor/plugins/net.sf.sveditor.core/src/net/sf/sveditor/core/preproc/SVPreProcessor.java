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
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IPreProcErrorListener;
import net.sf.sveditor.core.scanner.IPreProcMacroProvider;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ITextScanner;


public class SVPreProcessor extends AbstractTextScanner 
		implements ISVPreProcessor, ILogLevelListener, IPreProcErrorListener,
					ISVStringPreProcessor, ILogLevel {
	private SVDBIndexStats							fIndexStats;
	private ISVPreProcIncFileProvider				fIncFileProvider;
	private StringBuilder							fOutput;
	private int										fOutputLen;
	private StringBuilder							fCommentBuffer;
	private boolean									fInComment;
	private IDocCommentParser   					fDocCommentParser;
	private long									fCommentStart;
	private Set<String>								fTaskTags;

	// List of offset,file-id pairs
	private List<SVPreProcOutput.FileChangeInfo>	fFileMap;
	private List<String>							fFileList;
	private StringBuilder							fTmpBuffer;
	private List<String>							fMacroParams;
	private Stack<Integer>							fPreProcEn;
	private Stack<Long>								fPreProcLoc;
	private IPreProcMacroProvider					fMacroProvider;
	private SVSingleLevelMacroExpander				fMacroExpander;
	private LogHandle								fLog;
	private boolean									fDebugEn = false;
	
	private Stack<SVPreProc2InputData>				fInputStack;
	private boolean									fInputStackChanged;
	private SVPreProc2InputData						fInputCurr;
	private Set<String>								fMacroExpSet;
	private ISVPreProcFileMapper					fFileMapper;
	private Map<String, SVDBMacroDef>				fMacroMap = new HashMap<String, SVDBMacroDef>();
	private List<IPreProcListener>					fListeners;
	private boolean									fHaveListeners;
	
	private boolean									fEmitLineDirectives;
	
	private int										fLastFileId = 0;
	private int										fLastLineNo = 0;
	private boolean									fLastIncEn = false;
	
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

	public SVPreProcessor(
			String							filename,
			InputStream	 					input, 
			ISVPreProcIncFileProvider		inc_provider,
			ISVPreProcFileMapper			file_mapper) {
		fInputStack = new Stack<SVPreProc2InputData>();
		fMacroExpSet = new HashSet<String>();
		fOutput = new StringBuilder();
		fCommentBuffer = new StringBuilder();
		fDocCommentParser = new DocCommentParser();
		fTmpBuffer = new StringBuilder();
		fMacroParams = new ArrayList<String>();
		fPreProcEn = new Stack<Integer>();
		fPreProcLoc = new Stack<Long>();
		fFileMap = new ArrayList<SVPreProcOutput.FileChangeInfo>();
		fFileList = new ArrayList<String>();
		
		fEmitLineDirectives = true;

		fIncFileProvider 	= inc_provider;
		fFileMapper			= file_mapper;
		fListeners			= new ArrayList<IPreProcListener>();
	
		fMacroProvider  = defaultMacroProvider;
		defaultMacroProvider.setMacro("SVEDITOR", "");
		fMacroExpander = new SVSingleLevelMacroExpander();
		
		fLog = LogFactory.getLogHandle("SVPreProcessor2");
		fLog.addLogLevelListener(this);
		fDebugEn = fLog.isEnabled();
		
		fTaskTags = new HashSet<String>();
		fTaskTags.add("TODO");
		fTaskTags.add("FIXME");
		
		// Add the first file
		if (input != null) {
			enter_file(filename, input);
		}
	}
	
	private void init_vars() {
		fInputStack.clear();
		fMacroExpSet.clear();
		fOutput.setLength(0);
		fCommentBuffer.setLength(0);
		fTmpBuffer.setLength(0);
		fMacroParams.clear();
		fPreProcEn.clear();
		fPreProcLoc.clear();
		fFileMap.clear();
		fFileList.clear();
	}

	/**
	 * Implementation of the ISVStringPreProcessor interface
	 */
	@Override
	public String preprocess(InputStream in) {
		init_vars();
		
		enter_file("", in);
		
		preprocess();
		
		return fOutput.toString();
	}

	public void addListener(IPreProcListener l) {
		fListeners.add(l);
		fHaveListeners = true;
	}
	
	public void removeListener(IPreProcListener l) {
		fListeners.remove(l);
		fHaveListeners = (fListeners.size() > 0);
	}

	@Override
	public void setEmitLineDirectives(boolean emit) {
		fEmitLineDirectives = emit;
	}
	
	private void sendEvent(PreProcEvent ev) {
		for (IPreProcListener l : fListeners) {
			l.preproc_event(ev);
		}
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
		fOutput.setLength(0);
		fCommentBuffer.setLength(0);
		
		// First thing we do is emit a line directive.
		// This initializes everything for the output 
		emit_line();

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
							
							String S = fCommentBuffer.toString(); 

							if (end_comment1 == '*' && end_comment2 == '/') {
								// Remove trailing *
								fCommentBuffer.deleteCharAt(fCommentBuffer.length()-1);
								endComment();
								break;
							} else {
								if (ch == '\n') {
									output('\n');
								}
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
					if (ch == '"' && last_ch != '\\' && last_ch != '`') {
						// Enter string
						in_string = true;
					}
					if (ifdef_enabled && ch != -1) {
						output((char)ch);
					}
				}
			} else { // In String
				if (ch == '"' && last_ch != '\\' && last_ch != '`') {
					in_string = false;
				}
				if (ifdef_enabled && ch != -1) {
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
		
		SVPreProcOutput ret = new SVPreProcOutput(fOutput);
		ret.setFileTree(fInputCurr.getFileTree());
		
		// Clean up after any unbalanced pre-processor directives
		cleanup_preproc_leftovers();
	
		// Leave final file
		fInputCurr.close();
		
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
		
//		if (fDebugEn && fLog.getDebugLevel() >= ILogLevel.LEVEL_MAX) {
//			fLog.debug(ILogLevel.LEVEL_MAX, "PreProcessor Result:\n" + 
//					fOutput.toString() + "\n");
//		}
		
		return ret;
	}
	
	public SVDBFileTree getFileTree() {
		return fInputCurr.getFileTree();
	}
	
	public SVPreProc2InputData currentRealFile() {
		int i=fInputStack.size()-1;
		
//		while (i>=0 && fInputStack.get(i).getFileId() == -1) {
		while (i>=0 && fInputStack.get(i).getFileName().startsWith("Macro: ")) {
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
		if(!fInComment) { 
			return ; 
		}
		
		fInComment = false;
		String comment = fCommentBuffer.toString() ;
		Tuple<String,String> dc = new Tuple<String, String>(null, null);
		IDocCommentParser.CommentType type = fDocCommentParser.isDocCommentOrTaskTag(comment, dc) ;
		if (type != null && type != IDocCommentParser.CommentType.None) {
			String tag = dc.first();
			String title = dc.second();
			SVPreProc2InputData in = fInputCurr;
			long loc = fCommentStart;
			
			boolean is_task = fTaskTags.contains(tag);

			if (type == IDocCommentParser.CommentType.TaskTag && is_task) {
				// Actually a task marker
				String msg = tag + " " + title;
				SVDBMarker m = new SVDBMarker(MarkerType.Task, MarkerKind.Info, msg);

				// Fix the offset to the TODO in case it is not the first thing in a comment... typically in a multi-line comment
				int fileid = SVDBLocation.unpackFileId(loc);
				int line   = SVDBLocation.unpackLineno(loc);
				int pos    = SVDBLocation.unpackPos(loc);
				String lines[] = comment.split("\\n");
				for (String cl: lines)  {
					if (cl.contains(tag))  {
						break;
					}
					else  {
						line ++;
					}
				}
				loc = SVDBLocation.pack(fileid, line, pos);

				// Set location
				m.setLocation(loc);
				if (in.getFileTree() != null) {
					in.getFileTree().fMarkers.add(m);
				}
			} else if (type == IDocCommentParser.CommentType.DocComment && is_task) {
				String msg = tag + ": " + title;
				SVDBMarker m = new SVDBMarker(MarkerType.Task, MarkerKind.Info, msg);
				
				// Fix the offset to the TODO in case it is not the first thing in a comment... typically in a multi-line comment
				int fileid = SVDBLocation.unpackFileId(loc);
				int line   = SVDBLocation.unpackLineno(loc);
				int pos    = SVDBLocation.unpackPos(loc);
				String lines[] = comment.split("\\n");
				for (String cl: lines)  {
					if (cl.contains(tag))  {
						break;
					}
					else  {
						line ++;
					}
				}
				loc = SVDBLocation.pack(fileid, line, pos);

				// Set location
				m.setLocation(loc);
				if (in.getFileTree() != null) {
					in.getFileTree().fMarkers.add(m);
				}
			} else if (DocTopicManager.singularKeywordMap.containsKey(tag.toLowerCase())) {
				// Really a doc comment
				SVDBDocComment doc_comment = new SVDBDocComment(title, comment);

				doc_comment.setLocation(loc);
				if (in.getFileTree() != null) {
					in.getFileTree().getSVDBFile().addChildItem(doc_comment);
				}
			}
		} 
	}
	
	private void handle_preproc_directive() {
		int ch = -1;
		boolean have_ws = false;
		String buffer_macro_name = (fInputCurr != null)?fInputCurr.getFileName():null;
		
		if (fInputStackChanged) {
			update_macro_exp_set();
			fInputStackChanged = false;
		}
		
		while ((ch = get_ch()) != -1 && Character.isWhitespace(ch)) { 
			have_ws = true;
		}
		long scan_loc = getLocation();
	
		String type;
		if (ch == -1) {
			type = "";
		} else {
			// 
			// Don't want to get thrown off by something like
			// `  `MY_MACRO
			if (!have_ws && (ch == '`' || ch == '"')) {
				type = "" + (char)ch;
			} else {
				type = readPreProcIdentifier(ch);
			}
	
			if (type == null) {
				type = "";
			}
		}
	
		if (type.equals("\"")) {
			// `" ==> "
			output('"');
		} else if (type.equals("`")) {
			// `` => ""
		} else if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
			handle_if_directive(scan_loc, type);
		} else if (type.equals("else")) {
			enter_else(scan_loc);
		} else if (type.equals("endif")) {
			leave_ifdef(scan_loc);
		} else if (fIgnoredDirectives.contains(type)) {
			// Skip entire line 
			readLine(get_ch());
		} else if (type.equals("define")) {
			handle_define_directive(scan_loc);
			emit_line();
		} else if (type.equals("include")) {		
			handle_include_directive(scan_loc);
		} else if (type.equals("__LINE__") || type.equals("__FILE__")) {
			if (ifdef_enabled()) {
				// Find the last non-macro output
				SVPreProc2InputData input = null;
				for (int i=fInputStack.size()-1; i>=0; i--) {
					if (!fInputStack.get(i).getFileName().startsWith("Macro:")) {
						input = fInputStack.get(i);
						break;
					}
				}
				
				if (type.equals("__FILE__")) {
					output("\"" + ((input!=null)?input.getFileName():"UNKNOWN") + "\"");
				} else {
					output("" + ((input!=null)?input.getLineNo():-1));
				}
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
			handle_macro_directive(scan_loc, type, buffer_macro_name);
		}
	}
	
	private void handle_define_directive(long scan_loc) {
		SVDBMacroDef m = new SVDBMacroDef();
		int ch;
		// TODO: save file?

		// TODO: line numbers
		ch = skipWhite(get_ch());
		
		m.setName(readIdentifier(ch));
		m.setLocation(scan_loc);
		
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
	}
	
	private void handle_if_directive(long scan_loc, String type) {
		// TODO: line number tracking
		int ch = skipWhite(get_ch());
		
		// TODO: evaluate the expression?
		String remainder = readPreProcIdentifier(ch);
		
		if (remainder != null) {
			remainder = remainder.trim();
		} else {
			remainder = "";
		}
	
		// Add a new entry to the referenced macros 
		add_macro_reference(remainder);
		SVDBMacroDef m = fMacroProvider.findMacro(remainder, -1);

		if (type.equals("ifdef")) {
			if (fDebugEn) {
				fLog.debug("ifdef \"" + remainder + "\": " + (m != null));
			}
			enter_ifdef(scan_loc, (m != null));
		} else if (type.equals("ifndef")) {
			if (fDebugEn) {
				fLog.debug("ifndef \"" + remainder + "\": " + (m == null));
			}
			enter_ifdef(scan_loc, (m == null));
		} else { // elsif
			enter_elsif(scan_loc, (m != null));
		}		
	}
	
	private void handle_include_directive(long scan_loc) {
		int ch = skipWhite(get_ch());
		
		if (ch == '`') {
			// Handle expanding macro call, then resume
			handle_preproc_directive();
			
			ch = skipWhite(get_ch());
		}
		
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
					
					SVPreProc2InputData curr_in = currentRealFile();
					if (defs != null) {
						// Add in the macros from the included file
						for (SVDBFileTreeMacroList l : defs.second()) {
							for (SVDBMacroDef m : l.getMacroList()) {
								addMacro(m);
							}
						}
					
						// TODO: Need to mark as a 'virtual' include?
						SVDBInclude svdb_inc = new SVDBInclude(inc);
						svdb_inc.setLocation(scan_loc);
						
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
							svdb_inc.setLocation(scan_loc);

							curr_in.getFileTree().getSVDBFile().addChildItem(svdb_inc);

							enter_file(in.first(), in.second());
						} else {
							// Recursive include and have exceeded the limit
							SVDBMarker m = new SVDBMarker(MarkerType.Error, 
									MarkerKind.MissingInclude,
									"Recursive inclusion of file " + inc);
							m.setLocation(scan_loc);
							curr_in.getFileTree().fMarkers.add(m);
							try {
								in.second().close();
							} catch (IOException e) {}
						}
					} else {
						SVDBMarker m = new SVDBMarker(MarkerType.Error, 
								MarkerKind.MissingInclude,
								"Failed to find include file " + inc);
						m.setLocation(scan_loc);
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
	}
	
	private void handle_macro_directive(
			long 		scan_loc, 
			String 		type,
			String		buffer_macro_name) {
		int ch;
		
		// Note: type="" occurs when no identifier followed the tick
		// macro expansion.
		// TODO: is TmpBuffer available?
		fTmpBuffer.setLength(0);
		
		fTmpBuffer.append('`');
		fTmpBuffer.append(type);
		
		boolean do_event = fHaveListeners;
		
		boolean skip_recursive =
				(buffer_macro_name != null && buffer_macro_name.equals("Macro: " + type)) ||
				(fMacroExpSet.contains("Macro: " + type));
		
		// If we're in a disabled section, don't try to expand
		if (skip_recursive) {
			// Omit input
		} else if (ifdef_enabled()) {
			// Read the full string
		
			// Add a reference for this macro
			add_macro_reference(type);
			
			if (do_event) {
				startCapture(-1);
			}

			SVDBMacroDef md = fMacroProvider.findMacro(type, -1);
			if (md == null && fInputCurr.getFileTree() != null) {
				SVDBMarker m = new SVDBMarker(MarkerType.Error, 
						MarkerKind.UndefinedMacro,
						"Macro " + type + " undefined");
				m.setLocation(scan_loc);

				fInputCurr.getFileTree().fMarkers.add(m);
			}
		
			boolean have_macro_params = false;
			if ((md == null) || (md.getParameters() != null && md.getParameters().size() > 0)) {
				// Try to read the parameter list
				ch = get_ch();
				// skip up to new-line or non-whitespace
				if (md == null) {
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
				
				if (md != null) {
					// TODO: parse the parameter definitions into a list
					fMacroParams.clear();
					// Load up the default values. 
					for (SVDBMacroDefParam p : md.getParameters()) {
						fMacroParams.add(p.getValue());
					}

					SVSingleLevelMacroExpander.parseMacroCallParams(this, fMacroParams);
					have_macro_params = true;
				} else if (ch == '(') { // undefined macro, but appears to be one with params
					readMacroParameters(fTmpBuffer, ch);
				} else {
					unget_ch(ch);
				}
			}
			
			PreProcEvent ev_s = null;
			if (do_event) {
				fTmpBuffer.append(endCapture());
				ev_s = new PreProcEvent(PreProcEvent.Type.BeginExpand);
				ev_s.pos = fOutput.length();
				ev_s.text = fTmpBuffer.toString();
				sendEvent(ev_s);
			}

			if (md == null) {
				// Leave a breadcrumb for the lexer
				output("`undefined");
			} else {
				if (fDebugEn) {
					fLog.debug("Use MacroExpander: \"" + 
							fTmpBuffer.toString() + "\"");
					fLog.debug("Use MacroExpander: def=\"" + md.getDef() + "\"");
				}
				
				String exp = fMacroExpander.expandMacro(md, fMacroParams);
				
				if (fDebugEn) {
					fLog.debug("Use MacroExpander: expansion=\"" + exp + "\"");
				}
				
				if (buffer_macro_name != null && buffer_macro_name.startsWith("Macro:")) {
					push_input(new SVPreProc2InputData(
							this, new StringInputStream(""), buffer_macro_name, -1, false));
				}
				
				SVPreProc2InputData in = new SVPreProc2InputData(
						this, new StringInputStream(exp), 
						"Macro: " + type, fInputCurr.getFileId(), false);
				in.setBeginEv(ev_s);
				push_input(in);
			}
		}
	}
	
	private void readMacroParameters(StringBuilder sb, int ch) {
		sb.append((char)ch);

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
				// Found an escaped newline. Just get rid of it
				if (ch == '\n' && last_ch == '\\') {
					// Something to skip
					if (sb.length() > 0 && 
							sb.charAt(sb.length()-1) == '\r') {
						// Remove extra line feed
						sb.setLength(sb.length()-1);
					}
					if (sb.length() > 0 && 
							sb.charAt(sb.length()-1) == '\\') {
						// Remove escape char
						sb.setLength(sb.length()-1);
					}
				} else {
					sb.append((char)ch);
				}
			}
			last_ch = ch;
		} while (ch != -1 && matchLevel > 0);		
	}
	
	public static void ReadMacroRef(
			StringBuilder 			sb, 
			ITextScanner 			s,
			IPreProcMacroProvider	mp) {
		int ch = s.get_ch();
		
		if (ch != '`') {
			// doesn't look right
			s.unget_ch(ch);
			return;
		}
	
		sb.append((char)ch);
		
		// Skip whitespace
		while ((ch = s.get_ch()) != -1 && Character.isWhitespace(ch)) { }
		
		String type = AbstractTextScanner.readPreProcIdentifier(s, ch);
		
		if (type == null) {
			type = "";
		}
		sb.append(type);
	
		SVDBMacroDef m = mp.findMacro(type, -1);
		
		if (m == null || m.getParameters().size() > 0) {
			// Try to read the parameter list
			ch = s.get_ch();
			// skip up to new-line or non-whitespace
			if (m == null) {
				// For undefined macros, only search up to end-of-line
				while (ch != -1 && Character.isWhitespace(ch) && ch != '\n') {
					ch = s.get_ch();
				}
			} else {
				// For defined macros, skip all whitespace
				while (ch != -1 && Character.isWhitespace(ch)) {
					ch = s.get_ch();
				}
			}

			if (ch == '(') {
				sb.append((char)ch);

				// Read the parameter list
				int matchLevel=1, last_ch = -1;
				boolean in_string = false;

				do {
					ch = s.get_ch();

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
						// Found an escaped newline. Just get rid of it
						if (ch == '\n' && last_ch == '\\') {
							// Something to skip
							if (sb.length() > 0 && sb.charAt(sb.length()-1) == '\r') {
								// Remove extra line feed
								sb.setLength(sb.length()-1);
							}
							if (sb.length() > 0 && sb.charAt(sb.length()-1) == '\\') {
								// Remove escape char
								sb.setLength(sb.length()-1);
							}
						} else {
							sb.append((char)ch);
						}
					}
					last_ch = ch;
				} while (ch != -1 && matchLevel > 0);
			} else if (m != null) {
				s.unget_ch(ch);
			} else {
				s.unget_ch(ch);
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
		SVPreProc2InputData in_data = new SVPreProc2InputData(
				this, in_b, filename, file_id);
		add_file_change_info(file_id, in_data.getLineNo());
		
		in_data.setFileTree(new SVDBFileTree(new SVDBFile(filename)));
		
		// Record the current state of the pre-processor
//		in_data.fFileTree.fMacroEntryState.putAll(fMacroMap);
	
		if (!fInputStack.empty()) {
			SVPreProc2InputData p_data = currentRealFile();
			in_data.getFileTree().setParent(p_data.getFileTree());
			p_data.getFileTree().addIncludedFileTree(in_data.getFileTree());
		}

		push_input(in_data);
	}
	
	private void cleanup_preproc_leftovers() {
		int file_id = fInputCurr.getFileId();
		long loc;
		while (fPreProcLoc.size() > 0 && 
				SVDBLocation.unpackFileId((loc = fPreProcLoc.peek())) == file_id) {
			
			// Leftovers indicates unbalanced directives
			fPreProcLoc.pop();
			fPreProcEn.pop();
			SVDBMarker m = new SVDBMarker(MarkerType.Error, 
					MarkerKind.UnbalancedDirective, 
					"Unbalanced pre-processor directive");
			
			if (fDebugEn) {
				fLog.debug("Cleanup pre-proc leftover @ " + 
						SVDBLocation.unpackLineno(loc));
			}
			m.setLocation(loc);
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
		
		SVPreProc2InputData curr_in = fInputStack.pop();

		// Send expand-end events when the relevant document is complete
		PreProcEvent ev_s;
		if ((ev_s = curr_in.getBeginEv()) != null) {
			if (fHaveListeners) {
				PreProcEvent ev_e = new PreProcEvent(PreProcEvent.Type.EndExpand);
				ev_e.pos = fOutput.length();
				ev_e.text = ev_s.text;
				sendEvent(ev_e);
			}			
		}
		fInputStackChanged = true;

		SVPreProc2InputData new_file = fInputStack.peek();
		fInputCurr = new_file;
		
		if (fDebugEn) {
			if (!curr_in.getFileName().startsWith("Macro:") && 
					(new_file == null || !new_file.getFileName().startsWith("Macro:"))) {
				fLog.debug("Leaving file " + curr_in.getFileName() + " and switching to " +
					((new_file != null)?new_file.getFileName():"NONE"));
			}
		}
		
		if (fInputStack.size() == 1) {
			emit_line();
		}
		
		int file_idx = fFileList.indexOf(new_file.getFileName());

		// We will not have registered ANONYMOUS files
		if (file_idx != -1) {
			int file_id = 0;
			
			if (fFileMapper != null) {
				file_id = fFileMapper.mapFilePathToId(new_file.getFileName(), true);
			}
			
			// Add a marker noting that we're switching to a new file
			emit_line(file_id, new_file.getLineNo(), 
					!new_file.getFileName().startsWith("Macro:"));
		}
	}
	
	private void push_input(SVPreProc2InputData in) {
		// Macro the beginning of the new file
		if (fInputCurr != null && !fInputCurr.getFileName().startsWith("Macro:")) {
			if (in.getFileName().startsWith("Macro:")) {
				// If we're entering a macro, then stamp the current file and lineno
				emit_line(fInputCurr.getFileId(), fInputCurr.getLineNo(), false);
			} else {
				// If not, then stamp the new file and lineno
				emit_line(in.getFileId(), in.getLineNo(), true);
			}
		}
		fInputStack.push(in);
		fInputCurr = in;
		fInputStackChanged = true;
	}
	
	private void add_macro_reference(String macro) {
		SVPreProc2InputData in = fInputCurr;
		
		if (fMacroProvider != null) {
			SVDBMacroDef def = fMacroProvider.findMacro(macro, -1);

			in.addReferencedMacro(macro, def);
		}
	}
	
	private void enter_ifdef(long scan_loc, boolean enabled) {
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
			fLog.debug("enter_ifdef: " + SVDBLocation.unpackLineno(scan_loc) + 
					" enabled=" + enabled + " pre=" + enabled_pre + 
					" post=" + ifdef_enabled() + " sz=" + fPreProcEn.size());
		}
		
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void leave_ifdef(long scan_loc) {
		boolean enabled_pre = ifdef_enabled();
		if (fPreProcEn.size() > 0) {
			fPreProcEn.pop();
			fPreProcLoc.pop();
		}
	
		if (fDebugEn) {
			fLog.debug("leave_ifdef: " + SVDBLocation.unpackLineno(scan_loc) + 
					" pre=" + enabled_pre + 
					" post=" + ifdef_enabled());
		}
		
		update_unprocessed_region(scan_loc, enabled_pre);
	}
	
	private void enter_elsif(long scan_loc, boolean enabled) {
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
	
	private void enter_else(long scan_loc) {
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
			fLog.debug("enter_else: " + SVDBLocation.unpackLineno(scan_loc) + 
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
	
	private void update_unprocessed_region(long scan_loc, boolean enabled_pre) {
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
		
		if (ch > 127) {
			ch = AbstractTextScanner.unicode2ascii(ch);
		}
		
		if (fCaptureEnabled && ch != -1) {
			fCaptureBuffer.append((char)ch);
		}
		
		return ch;
	}
	
	public void unget_ch(int ch) {
		fInputCurr.unget_ch(ch);
		
		if (fCaptureEnabled && ch != -1) {
			if (fCaptureBuffer.length() > 0) {
				fCaptureBuffer.setLength(fCaptureBuffer.length()-1);
			}
		}
			

		/*
		if (ch != -1 && fCaptureEnabled && fCaptureBuffer.length() > 0) {
			fCaptureBuffer.deleteCharAt(fCaptureBuffer.length()-1);
		}
		 */
	}
	
	private void output(int ch) {
		if (ch == '\n') {
			if (fOutput.length() > 0 && fOutput.charAt(fOutput.length()-1) == '\r') {
				fOutput.setLength(fOutput.length()-1);
			}
		}
		fOutput.append((char)ch);
		fOutputLen++;
	}
	
	private void output(String str) {
		for (int i=0; i<str.length(); i++) {
			output(str.charAt(i));
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
	
	public long getLocation() {
		return fInputCurr.getLocation();
	}
	
	
	@Override
	public int getFileId() {
		return -1;
	}

	@Override
	public int getLineno() {
		return fLineno;
	}

	@Override
	public int getLinepos() {
		return fLinepos;
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
	
	private void emit_line() {
		emit_line(fInputCurr.getFileId(), fInputCurr.getLineNo(), 
				!fInputCurr.getFileName().startsWith("Macro:"));
	}
	
	private void emit_line(
			int			fileid,
			int			lineno,
			boolean		en_inc) {
		if (fEmitLineDirectives) {
			fOutput.append("\n`line " + fileid + ":" + lineno + ":" + ((en_inc)?1:0) + "\n");
		}
	}
	
	private void update_macro_exp_set() {
		fMacroExpSet.clear();
	
		for (int i=0; i<fInputStack.size(); i++) {
			String name = fInputStack.get(i).getFileName();
			if (name.startsWith("Macro: ")) {
				fMacroExpSet.add(name);
			}
		}
	}

	@Override
	public void preProcError(String msg, String filename, int lineno) {
		// TODO Auto-generated method stub
		
	}
	
}
