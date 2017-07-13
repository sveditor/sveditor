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


package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ICharacterPairMatcher;

public class SVCharacterPairMatcher implements ICharacterPairMatcher {
	
	private final char					fPairs[];
	private final String				fComplexPairs[];
	private boolean						fSearchComplexPairs;		// Enable search for complex pairs
	
	private int							fStartPos;
	private int							fEndPos;
	private int							fAnchor;
	private String						fPartitioning = SVDocumentPartitions.SV_PARTITIONING;
	private String						fCommentPartitions[] = {
			SVDocumentPartitions.SV_MULTILINE_COMMENT,
			SVDocumentPartitions.SV_SINGLELINE_COMMENT
	};
	
	/**
	 * Defaults to verilog pairs
	 */
	public SVCharacterPairMatcher() {
		fPairs = new char[] {
		'{', '}',
		'<', '>',
		'[', ']',
		'(', ')'
		};
		fComplexPairs = new String[]  {
				"begin", "end"
		};
		fSearchComplexPairs = true;
	}
	
	public SVCharacterPairMatcher(char pairs[], String partitioning, String comment_partitions[]) {
		fPairs = pairs;
		fPartitioning = partitioning;
		fCommentPartitions = comment_partitions;
		// Default to no complex pairs
		fComplexPairs = new String[]  {
		};
		fSearchComplexPairs = false;
	}

	public void clear() {}

	public void dispose() {
		clear();
	}

	public int getAnchor() {
		return fAnchor;
	}

	public IRegion match(IDocument document, int offset) {
		IBIDITextScanner scanner = new SVDocumentTextScanner(document, fPartitioning, fCommentPartitions, "", offset, true, true);
		
		if ((document == null) || (offset < 0)) {
			
		}
		
		if (offset < 0) {
			return null;
		}
		
		if (document != null && matchPairsAt(scanner) && fStartPos != fEndPos) {
			return new Region(fStartPos, fEndPos - fStartPos + 1);
		}
		
		return null;
	}
	
	private boolean matchPairsAt(IBIDITextScanner scanner) {
		int i;
		int pairIndex = fPairs.length;
		
		boolean foundComplex = false;
	
		long pos = scanner.getPos();
		int curr_char = scanner.get_ch();
		String curr_word;
		scanner.seek(pos);
		scanner.setScanFwd(false);

		fStartPos = -1;
		fEndPos = -1;
		// get the char preceding the start position
		scanner.get_ch();
		int prev_char = scanner.get_ch(); // fDocument.getgetChar(Math.max(fOffset - 1, 0));
		
		// search for opening peer character next to the activation point
		for (i = 0; i < fPairs.length; i = i + 2) {
			if (prev_char == fPairs[i]) {
				fStartPos = (int)(pos-1);
				pairIndex = i;
			} else if (curr_char == fPairs[i]) {
				fStartPos = (int)pos;
				pairIndex = i;
			}
		}
		
		// search for closing peer character next to the activation point
		for (i = 1; i < fPairs.length; i = i + 2) {
			if (curr_char == fPairs[i]) {
				fEndPos = (int)(pos);
				pairIndex = i-1;
			} else if (prev_char == fPairs[i]) {
				fEndPos = (int)(pos-1);
				pairIndex = i-1;
			}
		}

		// Now check if we need to search for complex pairs (didn't find a simple pair)
		if (fSearchComplexPairs && (fStartPos == -1) && (fEndPos == -1) && 
				(
				((curr_char >= 'a') && (curr_char <= 'z')) ||
				((prev_char >= 'a') && (prev_char <= 'z'))
				)
				)  {
			scanner.seek(pos);
			// Check if we are at the start of a word
			if (!IsCharDelimiter(prev_char))  {
				scanner.setScanFwd(false);
				scanner.get_ch();		// Step to prevch
				
				// Scan back to start of current word
				curr_word = GetNextWord(scanner, true);
				scanner.setScanFwd(true);
				if (pos - curr_word.length() > 0)  {
					scanner.seek(pos-curr_word.length());
				}
				else  {
					scanner.seek(pos);
				}
			}
			else  {
				scanner.setScanFwd(true);
			}
			if ((curr_word = GetNextWord(scanner, false)) == null)  {
				return (false);
			}
			
			// Now check if we have a matching start item
			for (i=0; i<fComplexPairs.length; i++)  {
				if (fComplexPairs[i].equals(curr_word))  {
					// Even numbers, start
					if (i%2 == 0)  {
						fStartPos = (int) (scanner.getPos()-fComplexPairs[i].length()-1);
						pairIndex = i;
						break;
					}
					// Found an end
					else  {
						fEndPos = (int) (scanner.getPos());
						pairIndex = i-1;
						break;
					}
				}
			}
			// If we don't have a complex pair, return immediately
			if (i == fComplexPairs.length)  {
				return (false);
			}
			else  {
				foundComplex = true;
			}
		}

		
		// Found a start or end token, now look for it's complement
		if (foundComplex)  {
			if (fEndPos > -1) {
				fAnchor = RIGHT;
				scanner.setScanFwd(false);
				scanner.seek(fEndPos);
				fStartPos = searchForOpeningComplexPeer(scanner, fComplexPairs[pairIndex], fComplexPairs[pairIndex + 1]);
				if (fStartPos > -1) {
					return true;
				} else {
					fEndPos = -1;
				}
			} else if (fStartPos > -1) {
				fAnchor = LEFT;
				scanner.setScanFwd(true);
				scanner.seek(fStartPos);
				fEndPos = searchForClosingComplexPeer(scanner, fComplexPairs[pairIndex], fComplexPairs[pairIndex + 1]);
				if (fEndPos > -1) {
					return true;
				} else {
					fStartPos = -1;
				}
			}
		}
		else  {
			if (fEndPos > -1) {
				fAnchor = RIGHT;
				scanner.setScanFwd(false);
				scanner.seek(fEndPos);
				fStartPos = searchForOpeningPeer(scanner, fPairs[pairIndex], fPairs[pairIndex + 1]);
				if (fStartPos > -1) {
					return true;
				} else {
					fEndPos = -1;
				}
			} else if (fStartPos > -1) {
				fAnchor = LEFT;
				scanner.setScanFwd(true);
				scanner.seek(fStartPos);
				fEndPos = searchForClosingPeer(scanner, fPairs[pairIndex], fPairs[pairIndex + 1]);
				if (fEndPos > -1) {
					return true;
				} else {
					fStartPos = -1;
				}
			}
		}

		return false;
	}

	/**
	 * Basic search for ClosingPeer
	 */
	private int searchForClosingPeer(IBIDITextScanner scanner, char opening, char closing) {
		int depth = 0;

		int ch = 0;
		while (true) {
			while ((ch = scanner.get_ch()) != -1) {
				if (ch =='"') {
					int last_ch = ch;
					while ((ch = scanner.get_ch()) != -1) {
						if (ch == '"' && last_ch != '\\') {
							break;
						}
						last_ch = ch;
					}
				}

				if (ch == opening || ch == closing) {
					break;
				}
			}
			if (ch == -1) {
				return -1;
			}
			if (ch == opening) {
				depth++;
			} else {
				depth--;
			}
			if (depth == 0) {
				if (scanner.getPos() > 0) {
					return (int)(scanner.getPos()-1);
				} else {
					return (int)scanner.getPos();
				}
			}
		}
	}

	/**
	 * Basic search for OpeningPeer
	 */
	private int searchForOpeningPeer(IBIDITextScanner scanner, char opening, char closing) {
		int depth = 0;
		int ch = 0;
		while (true) {
			while ((ch = scanner.get_ch()) != -1) {
				if (ch =='"') {
					while ((ch = scanner.get_ch()) != -1) {
						if (ch == '"') { 
							int prev_ch = scanner.get_ch();
							if (prev_ch != '\\') {
								// not escaped quote, done
								scanner.unget_ch(prev_ch);
								break;
							}
						}
					}
				}
				if (ch == opening || ch == closing) {
					break;
				}
			}
			if (ch == -1) {
				return -1;
			}
			if (ch == closing) {
				depth++;
			} else {
				depth--;
			}
			if (depth == 0) {
				// Get word could be 
				return (int)(scanner.getPos()+1);
			}
		}
	}
	
	/**
	 * 
	 * @param scanner
	 * @param opening
	 * @param closing
	 * @return
	 */
	private int searchForClosingComplexPeer(IBIDITextScanner scanner, String opening, String closing) {
		int depth = 0;
		
		String curr_word;
		while (true) {
			while ((curr_word = GetNextWord(scanner, false)) != null) {
//				if (ch =='"') {
//					int last_ch = ch;
//					while ((ch = scanner.get_ch()) != -1) {
//						if (ch == '"' && last_ch != '\\') {
//							break;
//						}
//						last_ch = ch;
//					}
//				}
				
				if (curr_word.equals(opening) || curr_word.equals(closing)) {
					break;
				}
			}
			if (curr_word.equals("")) {
				return -1;
			}
			if (curr_word.equals(opening)) {
				depth++;
			} else {
				depth--;
			}
			if (depth == 0) {
				if (scanner.getPos() > 0) {
					return (int)(scanner.getPos()-2);
				} else {
					return (int)scanner.getPos();
				}
			}
		}
	}
	

	/**
	 * 
	 * @param scanner
	 * @param opening
	 * @param closing
	 * @return
	 */
	private int searchForOpeningComplexPeer(IBIDITextScanner scanner, String opening, String closing) {
		int depth = 0;
		String curr_word;
		while (true) {
			while ((curr_word = GetNextWord(scanner, true)) != null) {
//				if (curr_word =='"') {
//					while ((curr_word = scanner.get_curr_word()) != -1) {
//						if (curr_word == '"') { 
//							int prev_curr_word = scanner.get_curr_word();
//							if (prev_curr_word != '\\') {
//								// not escaped quote, done
//								scanner.unget_curr_word(prev_curr_word);
//								break;
//							}
//						}
//					}
//				}
				if (curr_word.equals(opening) || curr_word.equals(closing)) {
					break;
				}
			}
			if (curr_word.equals("")) {
				return -1;
			}
			if (curr_word.equals(closing)) {
				depth++;
			} else {
				depth--;
			}
			if (depth == 0) {
				return (int)(scanner.getPos()+2);
			}
		}
	}
	
	
	/**
	 * Searches for the next string.  Note that this will search up to the next delimiter, and skip over the delimiter
	 * 
	 * 
	 * @param scanner - handle to scanner
	 * @param boolean scanningBackwards - true = forward, false = backwards
	 * @return String containing current word.  Returns empty string if none found
	 */
	/**
	 * 
	 * @return
	 */
	private String GetNextWord (IBIDITextScanner scanner, boolean scanningBackwards)  {
		StringBuilder sb = new StringBuilder();
		int ch;
		boolean foundDelim = false;
		
		// Scan till we reach a non-delimiter
		while ((ch = scanner.get_ch()) != -1)  {
			foundDelim = false;
			// Scan through any delimiters under cursor till next non-delimiter
			foundDelim = IsCharDelimiter(ch);
			// Non-delimter found ... break out and start capturing data 
			if (!foundDelim)  {
				sb.append((char) ch);
				break;
			}
		}
			
		// Scan till we reach a delimiter
		while ((ch = scanner.get_ch()) != -1)  {
			
			// Scan through any delimiters under cursor till next non-delimiter
			foundDelim = IsCharDelimiter(ch);
		
			// If we haven't found a delimiter, add it to the string
			if (!foundDelim)  {
				sb.append((char) ch);
			}
			else  {
				// If we have been scanning backwards, reverse string
				if (scanningBackwards)  {
					sb = sb.reverse();
				}
				// Return what we have found
				return (sb.toString());
			}
		}
		
		// Reached start / end of file, check if we have something here, and return it if so
		if (sb.length() > 0)  {
			if (scanningBackwards)  {
				sb = sb.reverse();
			}
			return (sb.toString());
		}
		
		// No string, just return
		return (null);
		
	}
	/**
	 * Returns true if character is a non-word character
	 * 
	 * Words continue in the space a-z A-Z _ 0-9
	 * 
	 * @param ch
	 * @return
	 */
	private boolean IsCharDelimiter (int ch)  {
		if (((ch >= 'a') && (ch <= 'z')) ||  
		    ((ch >= 'A') && (ch <= 'Z')) ||  
		    ((ch >= '0') && (ch <= '9')) ||  
		    (ch == '_')
		    )  {
			return (false);
		}
		return (true);
	}
}
