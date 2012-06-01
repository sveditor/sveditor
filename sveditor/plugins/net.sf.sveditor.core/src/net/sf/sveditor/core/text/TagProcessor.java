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
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.templates.ITemplateParameterProvider;

public class TagProcessor {
	private List<ITemplateParameterProvider>		fProviders;
	
	public TagProcessor() {
		fProviders = new ArrayList<ITemplateParameterProvider>();
	}
	
	public void addParameterProvider(ITemplateParameterProvider p) {
		fProviders.add(p);
	}

	public void removeParameterProvider(ITemplateParameterProvider p) {
		fProviders.remove(p);
	}
	
	public String process(String in) {
		StringInputStream in_str = new StringInputStream(in);
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		try {
			process(in_str, out);
		} catch (IOException e) { }
		
		return out.toString();
	}
	
	public int process(InputStream in, OutputStream out) throws IOException {
		int ch;
		int n_replacements = 0;
		StringBuilder sb = new StringBuilder();
		
		while ((ch = in.read()) != -1) {
			if (ch == '$') {
				int ch2 = in.read();
				
				if (ch2 == '{') {
					sb.setLength(0);

					for (int i=0; i<80; i++) {

						if ((ch = in.read()) == '}' || ch == -1) {
							break;
						}
						sb.append((char)ch);
					}

					String val = sb.toString();
					if (ch == '}') {
						String key = val;
						String args = null;
						if (key.indexOf(':') != -1) {
							args = key.substring(key.indexOf(':')+1);
							key = key.substring(0, key.indexOf(':'));
						}
						if (containsKey(key)) {
							out.write(getParameterValue(key, args).getBytes());
							n_replacements++;
						} else {
							out.write('$');
							out.write('{');
							out.write(val.getBytes());
							out.write('}');
						}
					} else {
						out.write('$');
						out.write('{');
						out.write(val.getBytes());
						if (ch != -1) {
							out.write((char)ch);
						}
					}
				} else {
					out.write((char)ch);
					if (ch2 != -1) {
						out.write((char)ch2);
					}
				}
			} else {
				out.write((char)ch);
			}
		}
		
		return n_replacements;
	}
	
	private boolean containsKey(String key) {
		for (ITemplateParameterProvider p : fProviders) {
			if (p.providesParameter(key)) {
				return true;
			}
		}
		return false;
	}
	
	private String getParameterValue(String key, String args) {
		for (ITemplateParameterProvider p : fProviders) {
			if (p.providesParameter(key)) {
				return p.getParameterValue(key, args);
			}
		}
		return null;
	}
}
