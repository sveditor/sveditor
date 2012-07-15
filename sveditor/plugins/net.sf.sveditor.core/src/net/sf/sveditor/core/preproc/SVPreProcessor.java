package net.sf.sveditor.core.preproc;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVPreProcessor extends AbstractTextScanner {
	private IDefineProvider				fDefineProvider;
	private String						fFileName;
	private InputStream					fInput;
	private StringBuilder				fOutput;
	private List<Integer>				fLineMap;
	private StringBuilder				fTmpBuffer;
	private List<String>				fParamList;
	private Stack<Integer>				fPreProcEn;
	private int						fLineno = 1;
	private int						fLastCh;
	private int						fUngetCh[] = {-1,-1};
	private byte						fInBuffer[];
	private int						fInBufferIdx;
	private int						fInBufferMax;

	private static final int    PP_DISABLED 			= 0;
	private static final int    PP_ENABLED  			= 1;
	
	// This bit is set when we are within a disabled section.
	// It's impossible for anything in a sub-section to be enabled
	private static final int    PP_CARRY    			= 2;
	
	// This bit is set when a block within this level of conditionals
	// has been taken (ie `ifdef (true) ... ; `ifndef (false))
	private static final int	PP_THIS_LEVEL_EN_BLOCK 	= 4;
	
	public SVPreProcessor(
			InputStream	 	input, 
			String			filename,
			IDefineProvider define_provider) {
		fOutput = new StringBuilder();
		fTmpBuffer = new StringBuilder();
		fInput = input;
		fDefineProvider = define_provider;
		fParamList = new ArrayList<String>();
		fFileName = filename;
		fPreProcEn = new Stack<Integer>();
		fLineMap = new ArrayList<Integer>();
		fInBuffer = new byte[8*1024];
		fInBufferIdx = 0;
		fInBufferMax = 0;
	}
	
	public SVPreProcOutput preprocess() {
		int ch, last_ch = -1;
		int end_comment[] = {-1, -1};
		boolean in_string = false;
		boolean ifdef_enabled = true;
		
		while ((ch = get_ch()) != -1) {
			if (!in_string) {
				// Handle comment
				if (ch == '/') {
					int ch2 = get_ch();

					if (ch2 == '/') {
						fOutput.append(' '); // ch
						while ((ch = get_ch()) != -1 && 
								ch != '\n' && ch != '\r') { }

						// Handle
						if (ch == '\r') {
							ch = get_ch();
							if (ch != '\n') {
								unget_ch(ch);
							}
						}
						ch = ' ';
						last_ch = ' ';
					} else if (ch2 == '*') {
						end_comment[0] = -1;
						end_comment[1] = -1;

						fOutput.append(' '); // ch

						while ((ch = get_ch()) != -1) {
							end_comment[0] = end_comment[1];
							end_comment[1] = ch;

							if (end_comment[0] == '*' && end_comment[1] == '/') {
								break;
							}
						}
						ch = ' ';
						last_ch = ' ';
					} else {
						unget_ch(ch2);
					}
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
		}
		
		return new SVPreProcOutput(fOutput, fLineMap);
	}
	
	private void handle_preproc_directive() {
		int ch = -1;
	
		String type = readIdentifier(get_ch());
		
		if (type.equals("ifdef") || type.equals("ifndef") || type.equals("elsif")) {
		
			// TODO: line number tracking
			ch = skipWhite(get_ch());
			
			// TODO: evaluate the expression?
			// String remainder = readLine_ll(ch).trim();
			String remainder = readIdentifier(ch);
			
			if (remainder != null) {
				remainder = remainder.trim();
			} else {
				remainder = "";
			}
			
			if (type.equals("ifdef")) {
				if (fDefineProvider != null) {
					enter_ifdef(fDefineProvider.isDefined(
							remainder, fLineno));
				} else {
					enter_ifdef(false);
				}
			} else if (type.equals("ifndef")) {
				if (fDefineProvider != null) {
					enter_ifdef(!fDefineProvider.isDefined(
							remainder, fLineno));
				} else {
					enter_ifdef(true);
				}
			} else { // elsif
				if (fDefineProvider != null) {
					enter_elsif(fDefineProvider.isDefined(
							remainder, fLineno));
				} else {
					enter_elsif(false);
				}
			}
		} else if (type.equals("else")) {
			enter_else();
		} else if (type.equals("endif")) {
			leave_ifdef();
		} else if (SVPreProcScanner.fIgnoredDirectives.contains(type)) {
			// Skip entire line 
			readLine(get_ch());
		} else if (type.equals("define")) {
			String def_id = null;

			// TODO: line numbers
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
						fParamList.add(p);
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
		} else if (type.equals("include")) {
			ch = skipWhite(get_ch());
			
			if (ch == '"') {
				String inc = readString(ch);

				if (inc.length() > 2) {
					inc = inc.substring(1, inc.length()-1);
				} else {
					inc = "";
				}
	
				/** TODO: 
				if (ifdef_enabled()) {
					if (fObserver != null) {
						fObserver.preproc_include(inc);
					}
				}
				 */
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
							enter_ifdef(false);
						} else if (id.equals("end_protected")) {
							leave_ifdef();
						}
					}
				}
			}
		} else if (type.equals("protected")) {
			enter_ifdef(false);
		} else if (type.equals("endprotected")) {
			leave_ifdef();
		} else {
			// macro expansion.
			// TODO: is TmpBuffer available?
			fTmpBuffer.setLength(0);
			
			fTmpBuffer.append('`');
			fTmpBuffer.append(type);

			// If we're in a disabled section, don't try to expand
			if (ifdef_enabled()) {
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
					// ch = skipWhite_ll(ch);

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
						/** TODO:
						fDefineProvider.error("macro \"" + type +
								"\" should have parameters, but doesn't", 
								fScanLocation.getFileName(),
								fScanLocation.getLineNo());
						 */
						/** TODO:
						fLog.debug("[ERROR] macro \"" + type + 
						"\" should have parameters, but doesn't @ " +
							fScanLocation.getFileName() + ":" + 
							fScanLocation.getLineNo());
						 */
						unget_ch(ch);
					} else {
						unget_ch(ch);
					}
				}

				if (fDefineProvider != null) {
						try {
							// TODO:
//							fOutput.append(fTmpBuffer);
							fOutput.append(fDefineProvider.expandMacro(
									fTmpBuffer.toString(), fFileName, fLineno));
							/**
							push_unacc(fDefineProvider.expandMacro(
									fTmpBuffer.toString(), 
									getLocation().getFileName(),
									getLocation().getLineNo()));
							 */
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
	
	private void enter_ifdef(boolean enabled) {
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
	}
	
	private void leave_ifdef() {
		if (fPreProcEn.size() > 0) {
			fPreProcEn.pop();
		}
	}
	
	private void enter_elsif(boolean enabled) {
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
	}
	
	private void enter_else() {
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
	}
	
	private boolean ifdef_enabled() {
		if (fPreProcEn.size() == 0) {
			return true;
		} else {
			int e = fPreProcEn.peek();
			return ((e & PP_ENABLED) == PP_ENABLED);
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
		if (fUngetCh[0] != -1) {
			ch = fUngetCh[0];
			fUngetCh[0] = fUngetCh[1];
			fUngetCh[1] = -1;
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
				// Save a marker for the line in the line-map
				fLineMap.add(fOutput.length()-1);
				fLineno++;
			}
			fLastCh = ch;
		}
		
		return ch;
	}
	
	public void unget_ch(int ch) {
		if (fUngetCh[0] == -1) {
			fUngetCh[0] = ch;
		} else {
			fUngetCh[1] = fUngetCh[0];
			fUngetCh[0] = ch;
		}
	}

	/**
	 * Unused
	 */
	public ScanLocation getLocation() {
		// Unnecessary
		return new ScanLocation(fFileName, fLineno, 1);
	}

	/**
	 * Unused
	 */
	public long getPos() {
		return -1;
	}
}
