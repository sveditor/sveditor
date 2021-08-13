/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.core.tagproc;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import org.sveditor.core.StringInputStream;

public class TagProcessor {
	private TemplateParameterProvider				fBase;
	private List<ITemplateParameterProvider>		fProviders;
	
	public TagProcessor() {
		fBase = new TemplateParameterProvider();
		fProviders = new ArrayList<ITemplateParameterProvider>();
		fProviders.add(fBase);
	}
	
	public void addParameterProvider(ITemplateParameterProvider p) {
		fProviders.add(p);
	}

	public void removeParameterProvider(ITemplateParameterProvider p) {
		fProviders.remove(p);
	}
	
	public void setTag(String tag, String value) {
		fBase.setTag(tag, value);
	}
	
	public String process(String in) {
		InputStream in_str = new StringInputStream(in);
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		int substitutions = 0, iterations = 0;
		do {
			try {
				substitutions = process(in_str, out);
			} catch (IOException e) { }
			iterations++;
			
			if (substitutions > 0 && iterations < 100) {
				in_str = new ByteArrayInputStream(out.toByteArray());
				out = new ByteArrayOutputStream();
			}
		} while (substitutions > 0 && iterations < 100);
		
		return out.toString();
	}
	
	public int process(InputStream in, OutputStream out) throws IOException {
		int ch, unget_ch = -1;
		int n_replacements = 0;
		StringBuilder sb = new StringBuilder();
		
		while (true) {
			if (unget_ch != -1) {
				ch = unget_ch;
				unget_ch = -1;
			} else if ((ch = in.read()) == -1) {
				break;
			}

			if (ch == '$') {
				int ch2 = in.read();
				
				if (ch2 == '{') {
					sb.setLength(0);

					for (int i=0; i<80; i++) {

						if ((ch = in.read()) == '}' || ch == -1 ||
								!((ch >= 'a' && ch <= 'z') ||
								  (ch >= 'A' && ch <= 'Z') ||
								  (ch >= '0' && ch <= '9') ||
								  ch == '_' || ch == '.')) {
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
						// Unget the last char
						unget_ch = ch;
					}
				} else {
					out.write((char)ch);
					unget_ch = ch2;
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
