/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.text;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.StringInputStream;

public class TagProcessor {
	private Map<String, String>				fTagMap;
	
	public TagProcessor() {
		fTagMap = new HashMap<String, String>();
	}
	
	public void setTag(String tag, String value) {
		if (fTagMap.containsKey(tag)) {
			fTagMap.remove(tag);
		}
		fTagMap.put(tag, value);
	}
	
	public void appendTag(String tag, String value) {
		String val;
		if (fTagMap.containsKey(tag)) {
			val = fTagMap.get(tag);
			fTagMap.remove(tag);
		} else {
			val = "";
		}
		val += value;
		fTagMap.put(tag, val);
	}
	
	public String process(String in) {
		StringInputStream in_str = new StringInputStream(in);
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		try {
			process(in_str, out);
		} catch (IOException e) { }
		
		return out.toString();
	}
	
	public void process(InputStream in, OutputStream out) throws IOException {
		int ch;
		StringBuilder sb = new StringBuilder();
		
		while ((ch = in.read()) != -1) {
			if (ch == '@') {
				sb.setLength(0);
				
				for (int i=0; i<80; i++) {
					
					if ((ch = in.read()) == '@' || ch == -1) {
						break;
					}
					sb.append((char)ch);
				}
				
				String val = sb.toString();
				if (ch == '@') {
					if (fTagMap.containsKey(val)) {
						out.write(fTagMap.get(val).getBytes());
					} else {
						out.write('@');
						out.write(val.getBytes());
						out.write('@');
					}
				} else {
					out.write('@');
					out.write(val.getBytes());
					if (ch != -1) {
						out.write((char)ch);
					}
				}
			} else {
				out.write((char)ch);
			}
		}
	}
}
