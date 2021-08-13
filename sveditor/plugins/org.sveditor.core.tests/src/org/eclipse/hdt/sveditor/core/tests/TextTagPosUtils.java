/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.tests;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.StringInputStream;

public class TextTagPosUtils {
	private ByteArrayOutputStream			fStrippedData;
	private Map<String, Integer>			fPosMap;
	private Map<String, Integer>			fLineMap;
	private int								fUngetCh;
	private int								fLastCh;
	private int								fLineno;
	private int								fPos;
	private InputStream						fInputStream;
	
	public TextTagPosUtils(InputStream in) {
		fInputStream = in;
		
		fPosMap  = new HashMap<String, Integer>();
		fLineMap = new HashMap<String, Integer>();
		fStrippedData = new ByteArrayOutputStream();
		
		process();
	}
	
	public TextTagPosUtils(String in) {
		this(new StringInputStream(in));
	}
	
	public Map<String, Integer> getPosMap() {
		return fPosMap;
	}
	
	public int getTagPos(String tag) {
		if (!fPosMap.containsKey(tag)) {
			return -1;
		} else {
			return fPosMap.get(tag);
		}
	}
	
	public Map<String, Integer> getLineMap() {
		return fLineMap;
	}
	
	public InputStream openStream() {
		return new ByteArrayInputStream(fStrippedData.toByteArray());
	}
	
	public String getStrippedData() {
		return fStrippedData.toString();
	}

	private void process() {
		fUngetCh = -1;
		fLastCh  = -1;
		fLineno  = 1;
		fPos     = 0;
		int ch, ch2;
		StringBuilder	tmp = new StringBuilder();
		
		
		do {
			while ((ch = get_ch()) != -1 && ch != '<') {
				fStrippedData.write((char)ch);
			}
			
			ch2 = -1;
			if (ch == '<' && (ch2 = get_ch()) == '<') {
				tmp.setLength(0);
				tmp.append((char)ch);
				tmp.append((char)ch2);

				while ((ch = get_ch()) != -1 && Character.isJavaIdentifierPart(ch)) {
					tmp.append((char)ch);
				}

				ch2 = -1;
				if (ch == '>' && (ch2 = get_ch()) == '>') {
					String tag = tmp.substring(2);
					
					fPos -= (tmp.length() + 2); // start location
					fPosMap.put(tag, fPos);
					fLineMap.put(tag, fLineno);
				} else {
					for (int i=0; i<tmp.length(); i++) {
						fStrippedData.write(tmp.charAt(i));
					}
					fStrippedData.write((char)ch);
					unget_ch(ch2);
				}
			} else {
				unget_ch(ch2);
				if (ch != -1) {
					fStrippedData.write((char)ch);
				}
			}
			
			
		} while (ch != -1);

		/*
		fStrippedData.size();
		List<String> keys = new ArrayList<String>();
		keys.addAll(fPosMap.keySet());
		for (String key : keys) {
			int pos = fPosMap.get(key);
			if (pos >= fStrippedData.size()) {
				fPosMap.remove(key);
				fPosMap.put(key, fStrippedData.size()-1);
			}
		}
		 */
	}
	
	private int get_ch() {
		int ret = -1;
		
		if (fUngetCh != -1) {
			ret = fUngetCh;
			fUngetCh = -1;
			fLastCh = -1;
		} else {
			try {
				ret = fInputStream.read();
			} catch (IOException e) { }
			
			if (fLastCh == '\n') {
				fLineno++;
			}
			fLastCh = ret;
			fPos++;
			
			// System.out.println("char \"" + (char)ret + "\" @ " + fPos);
		}
		
		return ret;
	}
	
	private void unget_ch(int ch) {
		fUngetCh = ch;
	}
}
