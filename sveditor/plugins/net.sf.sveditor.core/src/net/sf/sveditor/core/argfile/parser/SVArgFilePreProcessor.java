package net.sf.sveditor.core.argfile.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.scanutils.AbstractTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVArgFilePreProcessor extends AbstractTextScanner {
	private String						fFileName;
	private InputStream					fInput;
	private StringBuilder				fOutput;
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
		
		if (!exp_brace) {
			unget_ch(ch);
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
			}
		} else {
			unget_ch(ch);
		}
		
		// Check whether the VariableProvider provides this variable
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
