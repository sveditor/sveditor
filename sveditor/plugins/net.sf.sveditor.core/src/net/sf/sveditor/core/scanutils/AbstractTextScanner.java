/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.scanutils;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.scanner.SVCharacter;


public abstract class AbstractTextScanner implements ITextScanner {
	protected StringBuilder				fTmpBuffer;
	protected StringBuilder				fCaptureBuffer;
	protected boolean					fCaptureEnabled;
	protected int						fLineno;
	protected int						fLinepos;
	protected int						fLastCh;
	protected boolean					fScanFwd;
	

	public AbstractTextScanner() {
		fTmpBuffer      = new StringBuilder();
		fCaptureBuffer  = new StringBuilder();
		fCaptureEnabled = false;
		fScanFwd = true;
		fLastCh  = -1;
		fLineno  = 1;
		fLinepos = 0;
	}
	
	public void init() {
		fCaptureEnabled = false;
	}
	
	public boolean getScanFwd() {
		return fScanFwd;
	}

	public void setScanFwd(boolean scanFwd) {
		fScanFwd = scanFwd;
	}
	
	@Override
	public int getLineno() {
		return fLineno;
	}

	@Override
	public int getLinepos() {
		return fLinepos;
	}

	@Override
	public int getFileId() {
		return -1;
	}
	
	public int skipWhite(int ch) {
		
		while (Character.isWhitespace(ch) || ch == '\\') {
			int tmp = get_ch();
			
			if (ch == '\\' && (tmp != '\r' && tmp != '\n')) {
				unget_ch(tmp);
				return ch;
			}
			ch = tmp;
		}
		return ch;
	}

	public String readIdentifier(int ci) {
		fTmpBuffer.setLength(0);
		
		if (fScanFwd) {
			if (!SVCharacter.isSVIdentifierStart(ci)) {
				unget_ch(ci);
				return null;
			}

			boolean in_ref = false;
			int last_ci = ci;

			fTmpBuffer.append((char)ci);

			while ((ci = get_ch()) != -1 && 
					(SVCharacter.isSVIdentifierPart(ci) || 
							ci == ':' ||
							(last_ci == '$' && ci == '{') ||
							(in_ref && ci == '}'))) {
				if (ci == ':') {
					int c2 = get_ch();
					if (c2 == ':') {
						fTmpBuffer.append("::");
					} else {
						unget_ch(c2);
						break;
					}
				} else {
					fTmpBuffer.append((char)ci);
				}
				
				in_ref |= (ci == '{' && last_ci == '$');
				in_ref &= !(in_ref && ci == '}');
				last_ci = ci;
			}
			unget_ch(ci);

			// Even though ':' can appear as part of the identifier, it
			// must not appear at the end of an identifier
			while (fTmpBuffer.length() > 0 && 
					fTmpBuffer.charAt(fTmpBuffer.length()-1) == ':') {
				unget_ch(':');
				fTmpBuffer.setLength(fTmpBuffer.length()-1);
			}
		} else {
			if (!SVCharacter.isSVIdentifierPart(ci)) {
				unget_ch(ci);
				return null;
			}

			fTmpBuffer.append((char)ci);

			while ((ci = get_ch()) != -1 && 
					(SVCharacter.isSVIdentifierPart(ci) || ci == ':')) {
				fTmpBuffer.append((char)ci);
			}
			unget_ch(ci);
		}

		if (fScanFwd) {
			return (fTmpBuffer.length()>0)?fTmpBuffer.toString():null;
		} else {
			if (fTmpBuffer.length() == 0) {
				return null;
			} else {
				return fTmpBuffer.reverse().toString();
			}
		}
	}
	

	public String readPreProcIdentifier(int ci) {
		fTmpBuffer.setLength(0);
		
		if (!SVCharacter.isSVIdentifierStart(ci)) {
			unget_ch(ci);
			return null;
		}

		fTmpBuffer.append((char)ci);

		while ((ci = get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ci)) {
			fTmpBuffer.append((char)ci);
		}
		unget_ch(ci);

		return (fTmpBuffer.length()>0)?fTmpBuffer.toString():null;
	}
	
	public static int readPreProcIdentifier(
			StringBuilder			sb,
			ITextScanner			scanner,
			int						ch) {
		if (!SVCharacter.isSVIdentifierStart(ch)) {
			return ch;
		}

		sb.append((char)ch);

		while ((ch = scanner.get_ch()) != -1 && 
				SVCharacter.isSVIdentifierPart(ch)) {
			sb.append((char)ch);
		}
		
		return ch;
	}
	
	public static String readPreProcIdentifier(ITextScanner s, int ci) {
		if (!SVCharacter.isSVIdentifierStart(ci)) {
			s.unget_ch(ci);
			return null;
		}
		
		StringBuilder sb = new StringBuilder();

		sb.append((char)ci);

		while ((ci = s.get_ch()) != -1 && SVCharacter.isSVIdentifierPart(ci)) {
			sb.append((char)ci);
		}
		s.unget_ch(ci);

		return (sb.length()>0)?sb.toString():null;
	}	

	public String readString(int ch) {
		fTmpBuffer.setLength(0);
		int last_ch = -1;
		
		if (ch != '"') {
			return null;
		}
		
		ch = get_ch();
		while (((ch != '"' && ch != '\n') || last_ch == '\\') && ch != -1) {
			if (last_ch == '\\' && ch == '"') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, '"');
				}
			} else if (last_ch == '\\' && ch == '\n') {
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\r') {
					fTmpBuffer.setLength(fTmpBuffer.length()-1);
				}
				if (fTmpBuffer.charAt(fTmpBuffer.length()-1) == '\\') {
					fTmpBuffer.setCharAt(fTmpBuffer.length()-1, ' ');
				}
			} else {
				fTmpBuffer.append((char)ch);
			}
			
			if (ch != '\r') {
				last_ch = ch;
			}
			
			ch = get_ch();
		}
		
		return fTmpBuffer.toString();
	}

	public void startCapture(int ch) {
		fCaptureEnabled = true;
		fCaptureBuffer.setLength(0);
		if (ch != -1) {
			fCaptureBuffer.append((char)ch);
		}
	}

	public String endCapture() {
		fCaptureEnabled = false;
		return fCaptureBuffer.toString();
	}

	public int skipPastMatch(String pair) {
		int begin = pair.charAt(0);
		int end = pair.charAt(1);
		int matchLevel = 1;
		int ch;
		
		do {
			ch = get_ch();
			if (ch == begin) {
				matchLevel++;
			} else if (ch == end) {
				matchLevel--;
			}
		} while (matchLevel > 0 && ch != -1);
		
		return get_ch();
	}
	
	private static final Map<Integer, Character>		Unicode2ASCI;
	static {
		Unicode2ASCI = new HashMap<Integer,Character>();
		Unicode2ASCI.put(0xAB, '"');
		Unicode2ASCI.put(0xAD, '-');
		Unicode2ASCI.put(0xB4, '\'');
		Unicode2ASCI.put(0xBB, '"');
		Unicode2ASCI.put(0xF7, '/');
		Unicode2ASCI.put(0x1C0, '|');
		Unicode2ASCI.put(0x1C3, '!');
		Unicode2ASCI.put(0x2B9, '\'');
		Unicode2ASCI.put(0x2BA, '"');
		Unicode2ASCI.put(0x2BC, '\'');
		Unicode2ASCI.put(0x2C4, '^');
		Unicode2ASCI.put(0x2C6, '^');
		Unicode2ASCI.put(0x2C8, '\'');
		Unicode2ASCI.put(0x2CB, '`');
		Unicode2ASCI.put(0x2CD, '_');
		Unicode2ASCI.put(0x2DC, '~');
		Unicode2ASCI.put(0x300, '`');
		Unicode2ASCI.put(0x301, '\'');
		// More here...
		Unicode2ASCI.put(0x2019, '\'');
		Unicode2ASCI.put(0x201B, '\'');
		Unicode2ASCI.put(0x201C, '"');
		Unicode2ASCI.put(0x201D, '"');
		Unicode2ASCI.put(0x201E, '"');
		Unicode2ASCI.put(0x201F, '"');
		Unicode2ASCI.put(0x2032, '\'');
		Unicode2ASCI.put(0x2033, '"');
		Unicode2ASCI.put(0x2036, '"');
		// More here...
		Unicode2ASCI.put(0x301D, '"');
		Unicode2ASCI.put(0x301E, '"');
		
	}
	
	public static int unicode2ascii(int ch) {
		Character ch_a = Unicode2ASCI.get(ch);
		if (ch_a != null) {
//			System.out.println("Map: " + (char)ch + " => " + ch_a.charValue());
			return ch_a.charValue();
		} else {
//			System.out.println("Unmapped unicode char: " + (char)ch + " " + ch);
			return ch;
		}
	}

}
