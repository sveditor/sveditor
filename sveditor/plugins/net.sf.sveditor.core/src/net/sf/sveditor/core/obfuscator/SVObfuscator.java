package net.sf.sveditor.core.obfuscator;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.ISVPreProcScannerObserver;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;
public class SVObfuscator {
	private List<String>					fInputPaths;
	private List<String>					fIncdirPaths;
	private String							fOutputPath;
	private ISVDBFileSystemProvider			fFSProvider;
	private Map<String, String>				fIdMap;
	private Map<String, String>				fFileMap;
	private Set<String>						fProcessedFiles;
	private LogHandle						fLog;
	private static final Set<String>		fBuiltinTasks;
	private Set<String>						fSeqPrefixes[];
	private Set<String> 					fOperatorSet;
	private Set<String>						fDefaultKeywordSet;
	
	static {
		fBuiltinTasks = new HashSet<String>();
	
		for (String tf : SVKeywords.getSystemCalls()) {
			fBuiltinTasks.add(tf);
		}
	}
	
	public SVObfuscator(ISVDBFileSystemProvider	fs_provider) {
		fInputPaths = new ArrayList<String>();
		fIncdirPaths = new ArrayList<String>();
		fFSProvider = fs_provider;
		fLog = LogFactory.getLogHandle("SVObfuscator");

		fOperatorSet = new HashSet<String>();
		fSeqPrefixes = new Set[] {
			fOperatorSet,
			new HashSet<String>(),
			new HashSet<String>()
		};

		for (String op : SVLexer.AllOperators) {
			if (op.length() == 3) {
				fSeqPrefixes[1].add(op.substring(0,2));
				fSeqPrefixes[2].add(op.substring(0,3));
			} else if (op.length() == 2) {
				fSeqPrefixes[1].add(op.substring(0,2));
			}
			fOperatorSet.add(op);
		}
		
		fDefaultKeywordSet = new HashSet<String>();
		for (String kw : SVKeywords.getKeywords()) {
			if (kw.endsWith("*")) {
				kw = kw.substring(0, kw.length() - 1);
			}
			fDefaultKeywordSet.add(kw);
		}
	}
	
	public void setOutputPath(String path) {
		fOutputPath = path;
	}
	
	public void addInputFile(String path) {
		fInputPaths.add(path);
	}

	public void process() {
		for (String path : fInputPaths) {
			
		}
	}

	private class SVPreProcDirectiveScanner extends AbstractTextScanner implements ISVScanner {

		private InputStream						fInput;
		private String							fFileName;
		private boolean							fInProcess;

		private int								fUngetCh = -1;
		private int								fLastCh  = -1;
		private int								fLineno;
		private StringBuffer					fTmpBuffer;
		private StringBuilder					fCommentBuffer;
		private List<Tuple<String, String>>		fParamList;
		private ISVPreProcScannerObserver		fObserver;
		private ISVScanner						fScanner;
		private IDefineProvider					fDefineProvider;
		private ScanLocation					fScanLocation;
		private byte							fInBuffer[];
		private int								fInBufferIdx;
		private int								fInBufferMax;
		public Set<String>						fIgnoredDirectives;
		private boolean							fDebugEn = true;
		private StringBuilder	fStringBuffer = new StringBuilder();

		public SVPreProcDirectiveScanner() {
			fTmpBuffer = new StringBuffer();
			fParamList = new ArrayList<Tuple<String,String>>();
			fScanLocation = new ScanLocation("", 0, 0);
			fCommentBuffer = new StringBuilder();
			fInBuffer = new byte[1024*8];
			fInBufferIdx = 0;
			fInBufferMax = 0;

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

		public void setScanner(ISVScanner scanner) {
			fScanner = scanner;
		}

		public ScanLocation getStmtLocation() {
			return fScanLocation;
		}

		public ScanLocation getStartLocation() {
			return fScanLocation;
		}

		public ScanLocation getLocation() {
			return new ScanLocation(fFileName, fLineno, 0);
		}

		public void setStmtLocation(ScanLocation location) {
			// Do nothing
		}

		public void init(InputStream in, String name) {
			fLineno = 1;
			fScanLocation.setLineNo(1);

			fTmpBuffer.setLength(0);

			fInput    = in;
			fFileName = name;

			fScanLocation.setFileName(name);
		}

		public void close() {
			try {
				if (fInput != null) {
					fInput.close();
				}
			} catch (IOException e) {}
		}

		public void process() {
			int				ch, last_ch = -1;
			int				end_comment[] = {-1, -1};
			boolean			in_string = false;
			//		StringBuilder	comment_buffer = new StringBuilder();
			//		boolean			in_comment_section = false;
			boolean			foundSingleLineComment = false;
			boolean			fIsNumber, fIsOperator, fIsIdentifier=false, fIsKeyword, fIsString=false, fIsDelayControl=false;
			String			fImage;

			fInProcess = true;

			if (fObserver != null) {
				fObserver.enter_file(fFileName);
			}

			while ((ch = get_ch()) != -1) {
				foundSingleLineComment = false ;
				if (!in_string) {
					// Handle comment
					if (ch == '/') {
						int ch2 = get_ch();

						if (ch2 == '/') {
							foundSingleLineComment = true ;
							while ((ch = get_ch()) != -1 && ch != '\n') { 
								fCommentBuffer.append((char)ch);
							}
							fCommentBuffer.append('\n');
							ch = ' ';
							last_ch = ' ';
						} else if (ch2 == '*') {
							end_comment[0] = -1;
							end_comment[1] = -1;
							while ((ch = get_ch()) != -1) {
								end_comment[0] = end_comment[1];
								end_comment[1] = ch;

								if (end_comment[0] == '*' && end_comment[1] == '/') {
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

					if (ch == '`') {
						handle_preproc_directive();
					} else {
						if (ch == '"' && last_ch != '\\') {
							// Enter string
							in_string = true;
						} else {
							// Read a number, operator, or identifier
							if (ch == '\'' || (ch >= '0' && ch <= '9')) {
								fIsNumber = true;

								if (ch == '\'') {
									int ch2 = get_ch();
									if (isUnbasedUnsizedLiteralChar(ch2)) {
										// unbased_unsigned_literal
										// nothing more to do
										append_ch(ch2);
									} else if (isBaseChar(ch2)) {
										ch = readBasedNumber(ch2);
										unget_ch(ch);
									} else {
										unget_ch(ch2);
										fIsOperator = true;
									}
								} else {
// TODO:									readNumber(ch, local_is_delay_ctrl);
									ch = get_ch();
									if (ch == 's') {
										// most likely 1step
										fIsNumber = false;
										fIsKeyword = true;
										fStringBuffer.append((char)ch);
										while ((ch = get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ch)) {
											fStringBuffer.append((char)ch);
										}
										unget_ch(ch);
									} else {
										unget_ch(ch);
									}
								}

								fImage = fStringBuffer.toString();
							} else if (fOperatorSet.contains(fStringBuffer.toString()) ||
									// Operators that can have up to three elements
									fSeqPrefixes[1].contains(fStringBuffer.toString()) ||
									fSeqPrefixes[2].contains(fStringBuffer.toString())) {
								// Probably an operator in some form
								operator();
							} else if (SVCharacter.isSVIdentifierStart(ch)) {
								int last_ch2 = ch;
								boolean in_ref = false;
								// Identifier or keyword
								
								while ((ch = get_ch()) != -1 && 
										(SVCharacter.isSVIdentifierPart(ch) ||
												(ch == '{' && last_ch2 == '$') ||
												(ch == '}' && in_ref))) {
									append_ch(ch);
									
									in_ref |= (last_ch2 == '$' && ch == '{');
									in_ref &= !(in_ref && ch == '}');
									
									last_ch2 = ch;
								}
								unget_ch(ch);
								// Handle case where we received a single '$'
								if (fStringBuffer.length() == 1 && fStringBuffer.charAt(0) == '$') {
									fIsOperator = true;
								} else {
									fIsIdentifier = true;
								}
							} else if (ch == '\\') {
								// Escaped identifier
								while ((ch = get_ch()) != -1 && !Character.isWhitespace(ch)) {
									append_ch(ch);
								}
								unget_ch(ch);
							}

							if (fStringBuffer.length() == 0 && !fIsString) {
// TODO:								fEOF = true;
								/*
								 * if (fEnableEOFException) { throw new EOFException(); }
								 */
								if (fDebugEn) {
									fLog.debug("EOF - " + getStartLocation().toString());
								}
								if (fDebugEn) {
									fLog.debug("<-- next_token_int()");
								}
//								return false;
							} else {
								fImage = fStringBuffer.toString();

								if (fIsIdentifier) {
									Set<String> kw = fDefaultKeywordSet;
									
									if ((fIsKeyword = kw.contains(fImage))) {
										if (SVKeywords.isSVKeyword(fImage)) {
											fIsIdentifier = false;
										}
									}
								}
								
								if (fDebugEn) {
									fLog.debug("next_token(): \"" + fImage + "\"");
								}
								if (fDebugEn) {
									fLog.debug("<-- next_token_int()");
								}
							}							
						}
					}
				} else {
					// In String
					if (ch == '"' && last_ch != '\\') {
						in_string = false;
					}
				}
				last_ch = ch;
			}

			if (fObserver != null) {
				fObserver.leave_file();
			}

			fInProcess = false;
		}
		
		private void append_ch(int ch) {
			// TODO:
		}
		
		private void operator() {
			int ch;
			int op_idx=0; // index of the op prefix to check

			if (fDebugEn) {
//TODO:				debug("operator: " + fStringBuffer.toString());
			}
			while (op_idx < 2) {
				// Add a character and check whether is a prefix for the next
				// sequence
				if ((ch = get_ch()) != -1) {
					append_ch(ch);
					if (fDebugEn) {
//TODO:						debug("  append: " + (char)ch + "  => " + fStringBuffer.toString());
					}
					if (!fSeqPrefixes[op_idx+1].contains(fStringBuffer.toString()) &&
							!fOperatorSet.contains(fStringBuffer.toString())) {
						// Doesn't match, so don't move forward
						unget_ch(ch);
						fStringBuffer.setLength(fStringBuffer.length()-1);
						if (fDebugEn) {
							fLog.debug("  \"" + (char)ch + "\" doesn't match");
						}
						break;
					} else {
						if (fDebugEn) {
//TODO:							fLog.debug("  " + (char)ch + " does match -- " + fStringBuffer.toString());
						}
					}
				} else {
					break;
				}

				op_idx++;
			}

			if (fDebugEn) {
//TODO:				debug("< operator: " + fStringBuffer.toString());
			}
//TODO:			fIsOperator = true;
			String val = fStringBuffer.toString();
			if (!fOperatorSet.contains(val)) {
				fLog.error("Problem with operator: " + fStringBuffer.toString());
			}

			if (val.equals("#")) {
				// May be a delay-control expression
				while ((ch = get_ch()) != -1 && Character.isWhitespace(ch)) { }
				if (ch >= '0' && ch <= '9') {
					// delay-control
//TODO:					fIsDelayControl = true;
				}
				unget_ch(ch);
			}
		}
		
		private boolean isBaseChar(int ch) {
			return (ch == 's' || ch == 'S' || ch == 'd' || ch == 'D' || ch == 'b'
				|| ch == 'B' || ch == 'o' || ch == 'O' || ch == 'h' || ch == 'H');
		}

		private boolean isUnbasedUnsizedLiteralChar(int ch) {
			return (ch == '0' || ch == '1' || ch == 'z' || ch == 'Z' || ch == 'x' || ch == 'X');
		}

		private int readBasedNumber(int ch) {
			/** TODO:
			int base;

			append_ch(ch);
			if (ch == 's' || ch == 'S') {
				ch = fScanner.get_ch();
				append_ch(ch);
			}

			if (!isBaseChar(ch)) {
				error("Unknown base digit " + (char) ch);
			}
			base = Character.toLowerCase(ch);

			// Skip whitespace
			while ((ch = fScanner.get_ch()) != -1 && Character.isWhitespace(ch)) {
			}

			if (base == 'd') {
				ch = readDecNumber(ch);
			} else if (base == 'h') {
				ch = readHexNumber(ch);
			} else if (base == 'o') {
				ch = readOctNumber(ch);
			} else if (base == 'b') {
				ch = readBinNumber(ch);
			}

			return ch;
			 */
			return -1;
		}
		
		private String readLine(int ci) {
			int last_ch = -1;

			fTmpBuffer.setLength(0);

			// Skip any leading whitespace. Do not include
			// in the
			while (ci != -1 && (ci == ' ' || ci == '\t')) {
				last_ch = ci;
				ci = get_ch();
			}

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

		private String readString_ll(int ci) {
			fTmpBuffer.setLength(0);
			int last_ch = -1;

			if (ci != '"') {
				return null;
			}

			fTmpBuffer.append((char)ci);

			ci = get_ch();
			while ((ci != '"' && ci != '\n' && ci != -1) || last_ch == '\\') {
				if (last_ch == '\\' && ci == '"') {
					if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
						fTmpBuffer.setCharAt(fTmpBuffer.length()-1, '"');
					}
				} else if (last_ch == '\\' && ci == '\n') {
					if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
						fTmpBuffer.setLength(fTmpBuffer.length()-1);
					}
					if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
						fTmpBuffer.setCharAt(fTmpBuffer.length()-1, ' ');
					}
				} else {
					fTmpBuffer.append((char)ci);
				}

				if (ci != '\r') {
					last_ch = ci;
				}

				ci = get_ch();
			}

			if (ci != -1 && ci != '\n' && ci != '\r') {
				fTmpBuffer.append((char)ci);
			}

			return fTmpBuffer.toString();
		}

		private void handle_preproc_directive() {
			int ch = -1;

			// Skip any whitespace (up to end-of-line) between
			// the ` and the directive
			while ((ch = get_ch()) != -1 && Character.isWhitespace(ch)) { }

			if (ch == -1) {
				return;
			}

			String type = readIdentifier(ch);

			if (type == null) {
				type = "";
			}

			fScanLocation.setLineNo(fLineno);

			if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
				ch = skipWhite(get_ch());

				// TODO: evaluate the expression?
				// String remainder = readLine_ll(ch).trim();
				String remainder = readIdentifier(ch);

				if (remainder != null) {
					remainder = remainder.trim();
				} else {
					remainder = "";
				}
			} else if (type.equals("else")) {
			} else if (type.equals("endif")) {
			} else if (fIgnoredDirectives.contains(type)) {
				// Skip entire line 
				readLine(get_ch());
			} else if (type.equals("define")) {
				String def_id = null;

				// Push the line number up to the scanner
				if (fScanner != null) {
					fScanner.setStmtLocation(getStmtLocation());
				}

				ch = skipWhite(get_ch());

				def_id = readIdentifier(ch);

				fParamList.clear();

				ch = get_ch();

				if (ch == '(') {
					// Has parameters

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
							fParamList.add(new Tuple<String, String>(p, dflt));
						}

						ch = skipWhite(get_ch());
					} while (ch == ',');

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

				if (fObserver != null) {
					fObserver.preproc_define(def_id, fParamList, define);
				}
			} else if (type.equals("include")) {
				ch = skipWhite(get_ch());

				if (ch == '"') {
					String inc = readString_ll(ch);

					if (inc.length() >= 2) {
						inc = inc.substring(1, inc.length()-1);
					}

					// TODO: Add include path
				}
			} else if (type.equals("__LINE__")) {
			} else if (type.equals("__FILE__")) {
			} else if (type.equals("pragma")) {
				ch = skipWhite(get_ch());
				String id = readIdentifier(ch);

				if (id != null) {
					// Ignore everything in the 'protected' region. 
					// Not much we can meaningfully show...
					if (id.equals("protect")) {
						ch = skipWhite(get_ch());

						id = readIdentifier(ch);
					}
				}
			} else if (type.equals("protected")) {
			} else if (type.equals("endprotected")) {
			} else {
				// macro expansion.
				// TODO: is TmpBuffer available?
				fTmpBuffer.setLength(0);

				fTmpBuffer.append('`');
				fTmpBuffer.append(type);

				// If we're in a disabled section, don't try to expand
				// Read the full string

				boolean is_defined = (fDefineProvider != null)?fDefineProvider.isDefined(type, fLineno):false;
				if (fDefineProvider != null && 
						(fDefineProvider.hasParameters(type, fLineno) || !is_defined)) {
					// Try to read the parameter list
					ch = get_ch();
					// skip up to new-line or non-whitespace
					while (ch != -1 && Character.isWhitespace(ch) && ch != '\n') {
						ch = get_ch();
					}
					// ch = skipWhite(ch);

					if (ch == '(') {
						fTmpBuffer.append((char)ch);

						int matchLevel=1;

						do {
							ch = get_ch();

							if (ch == '(') {
								matchLevel++;
							} else if (ch == ')') {
								matchLevel--;
							}

							if (ch != -1) {
								fTmpBuffer.append((char)ch);
							}
						} while (ch != -1 && matchLevel > 0);
					} else if (is_defined) {
						fDefineProvider.error("macro \"" + type +
								"\" should have parameters, but doesn't", 
								fScanLocation.getFileName(),
								fScanLocation.getLineNo());
						fLog.debug("[ERROR] macro \"" + type + 
								"\" should have parameters, but doesn't @ " +
								fScanLocation.getFileName() + ":" + 
								fScanLocation.getLineNo());
						unget_ch(ch);
					} else {
						unget_ch(ch);
					}
				}
			}
		}

		public int get_ch() {
			int ch = -1;

			if (!fInProcess) {
				throw new RuntimeException(
						"SVPreProcDirectiveScanner.get_ch() cannot be called externally");
			}

			if (fUngetCh != -1) {
				ch = fUngetCh;
				fUngetCh = -1;
			} else {
				if (fInBufferIdx >= fInBufferMax) {
					// Time to read more data
					try {
						fInBufferMax = fInput.read(fInBuffer, 0, fInBuffer.length);
						fInBufferIdx = 0;
					} catch (IOException e) {}
				}
				if (fInBufferIdx < fInBufferMax) {
					ch = fInBuffer[fInBufferIdx++];
				} else {
					ch = -1;
				}
				if (fLastCh == '\n') {
					fLineno++;
				}
				fLastCh = ch;
			}

			if (ch != -1 && fCaptureEnabled) {
				fCaptureBuffer.append((char)ch);
			}

			return ch;
		}

		public void unget_ch(int ch) {
			fUngetCh = ch;

			if (ch != -1 && fCaptureEnabled && fCaptureBuffer.length() > 0) {
				fCaptureBuffer.deleteCharAt(fCaptureBuffer.length()-1);
			}
		}

		// Unused
		public long getPos() {
			return -1;
		}

	}	
}
