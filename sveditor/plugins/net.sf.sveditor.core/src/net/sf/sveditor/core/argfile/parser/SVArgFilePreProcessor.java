package net.sf.sveditor.core.argfile.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVArgFilePreProcessor extends AbstractTextScanner {
	private String						fFileName;
	private InputStream					fInput;
	private StringBuilder				fOutput;
	/**
	 * Contains a map of indexes into the output at which lines start
	 */
	private List<Integer>				fLineMap;
	private StringBuilder				fTmpBuffer;
	private int						fLineno = 1;
	private int						fLastCh;
	private int						fUngetCh[] = {-1,-1};
	private byte						fInBuffer[];
	private int						fInBufferIdx;
	private int						fInBufferMax;
	private boolean					fInPreProcess;
	private ISVArgFileVariableProvider	fVarProvider;
	private boolean					fDebugEn = true;
	private LogHandle					fLog;

	public SVArgFilePreProcessor(
			InputStream	 	input, 
			String			filename,
			ISVArgFileVariableProvider var_provider) {
		fOutput = new StringBuilder();
		fTmpBuffer = new StringBuilder();
		fInput = input;
		fFileName = filename;
		fVarProvider = var_provider;
		fLineMap = new ArrayList<Integer>();
		fInBuffer = new byte[8*1024];
		fInBufferIdx = 0;
		fInBufferMax = 0;
		fLog = LogFactory.getLogHandle("SVArgFilePreProcessor");
	}
	
	public SVArgFilePreProcOutput preprocess() {
		int ch, last_ch = -1;
		int end_comment[] = {-1, -1};
		
		fInPreProcess = true;
		
		while ((ch = get_ch()) != -1) {
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
					ch = '\n';
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

			if (ch == '$') {
				// Expand a variable
				handle_variable_ref();
			} else {
				fOutput.append((char)ch);
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
		
		fInPreProcess = false;
		
		return new SVArgFilePreProcOutput(fOutput, fLineMap);
	}
	
	private void handle_variable_ref() {
		int ch = get_ch();
		boolean exp_brace = (ch == '{');
		
		fTmpBuffer.setLength(0);
		fTmpBuffer.append('$');
		
		if (!exp_brace) {
			unget_ch(ch);
		} else {
			fTmpBuffer.append('{');
		}
		
		while ((ch = get_ch()) != -1) {
			if (exp_brace) {
				if (Character.isWhitespace(ch) || ch == '}') {
					break;
				}
			} else {
				if (!(
						(ch >= 'a' && ch <= 'z') ||
						(ch >= 'A' && ch <= 'Z') ||
						(ch >= '0' && ch <= '9') ||
						(ch == '_'))) {
					break;
				}
			}
			fTmpBuffer.append((char)ch);
		}
		
		if (exp_brace) {
			if (ch != '}') {
				// TODO: Error
				unget_ch(ch);
			} else {
				fTmpBuffer.append((char)ch);
			}
		} else {
			unget_ch(ch);
		}

		// Now, submit the variable to the expansion logic
		String val = expand_variable(fTmpBuffer.toString());
		fOutput.append(val);
		
		// Check whether the VariableProvider provides this variable
		/*
		String var = fTmpBuffer.toString();
		if (fVarProvider != null) {
			if (fVarProvider.providesVar(var)) {
				String val = fVarProvider.expandVar(var);
				fOutput.append(val);
			} else {
				// TODO: Error -- no variable provided
			}
		} else {
			// TODO: 
			fOutput.append(fTmpBuffer);
		}
		 */
	}
	
	private String expand_variable(String in) {
		int refs;
		StringBuilder out = new StringBuilder(in);
		Set<String> exp_vars = new HashSet<String>();
		
		do {
			refs = 0;
			for (int i=0; i<out.length(); i++) {
				if (charAt(out, i) == '$') {
					int start=-1, end=-1;
					i++;
					boolean exp_brace = (charAt(out, i) == '{');
					
					if (exp_brace) {
						i++;
					}
					start = i;
					
					while (i < out.length()) {
						if (exp_brace) {
							if (charAt(out, i) == '}' || Character.isWhitespace(charAt(out, i))) {
								break;
							}
						} else {
							char ch = charAt(out, i);
							if (!(
									(ch >= 'a' && ch <= 'z') ||
									(ch >= 'A' && ch <= 'Z') ||
									(ch >= '0' && ch <= '9') ||
									(ch == '_'))) {
								break;
							}
						}
						i++;
					}
					
					if (i < out.length()) {
						end = i;
					} else {
						end = out.length();
					}
				
					/*
					if (exp_brace && charAt(out, end-1) != '}') {
						// TODO: error
					} 
					 */
			
					String key = out.substring(start, end);
					if (fDebugEn) {
						fLog.debug("key=" + key);
					}
					if (!exp_vars.contains(key)) {
						refs++;
						exp_vars.add(key);
						String no_val = "$" + ((exp_brace)?"{":"") +
										key + ((exp_brace)?"}":"");
						String val = no_val;
						
						if (fVarProvider != null) {
							if (fVarProvider.providesVar(key)) {
								val = fVarProvider.expandVar(key);
							}
						}
						
						int replace_start = start - ((exp_brace)?2:1);
						int replace_end = end + ((exp_brace)?1:0);
						
						out.replace(replace_start, replace_end, val);
						if (fDebugEn) {
							fLog.debug("post-replace: " + out.toString());
						}
						i += (val.length()-no_val.length());
					} else {
						// TODO: Recursive expansion
					}
				}
			}
		} while (refs > 0);
		
		return out.toString();
	}
	
	private static char charAt(StringBuilder sb, int idx) {
		if (idx < 0 || idx >= sb.length()) {
			return Character.MAX_VALUE;
		} else {
			return sb.charAt(idx);
		}
	}
	
	public int get_ch() {
		int ch = -1;
		
		if (!fInPreProcess) {
			throw new RuntimeException("Cannot call SVPreProcessor.get_ch() outside preprocess()");
		}
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
					if (fInBufferMax <= 0) {
						fInput.close();
					}
				} catch (IOException e) {}
			}
			if (fInBufferIdx < fInBufferMax) {
				ch = fInBuffer[fInBufferIdx++];
			} else {
				ch = -1;
			}
			if (fLastCh == '\n') {
				// Save a marker for the line in the line-map
				System.out.println("Newline @ \"" + (char)ch + "\"");
				System.out.println(">> Current Output:");
				System.out.println(fOutput.toString());
				System.out.println("<< Current Output:");
				fLineMap.add(fOutput.length()-1);
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
		if (fUngetCh[0] == -1) {
			fUngetCh[0] = ch;
		} else {
			fUngetCh[1] = fUngetCh[0];
			fUngetCh[0] = ch;
		}

		if (ch != -1 && fCaptureEnabled && fCaptureBuffer.length() > 0) {
			fCaptureBuffer.deleteCharAt(fCaptureBuffer.length()-1);
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
