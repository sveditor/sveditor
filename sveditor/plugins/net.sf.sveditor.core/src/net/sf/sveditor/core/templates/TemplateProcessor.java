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


package net.sf.sveditor.core.templates;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.text.TagProcessor;

public class TemplateProcessor {
	private ITemplateFileCreator			fStreamProvider;

	private static final String							fDefaultFileHeader =
"/****************************************************************************\n" +
" * ${filename}\n" +
" ****************************************************************************/";
	
	
	public TemplateProcessor(ITemplateFileCreator provider) {
		fStreamProvider = provider;
	}
	
	public static List<String> getOutputFiles(TemplateInfo template, TagProcessor proc) {
		List<String> ret = new ArrayList<String>();
		
		for (Tuple<String, String> t : template.getTemplates()) {
			String name = proc.process(t.second());
			ret.add(name);
		}
		
		return ret;
	}
	
	public void process(TemplateInfo template, TagProcessor proc) {
		TemplateParameterProvider local_p = new TemplateParameterProvider();
		proc.addParameterProvider(local_p);
		/*
		if (!proc.hasTag("file_header")) {
			proc.setTag("file_header", fDefaultFileHeader);
		}
		 */
		
		for (Tuple<String, String> t : template.getTemplates()) {
			int n_replacements = 0;
			String templ = t.first();
			String name = proc.process(t.second());
		
			name = name.trim();
			
			local_p.setTag("filename", name);

			InputStream in = template.openTemplate(templ);
			ByteArrayInputStream  in_t = readInputStream(in);
			ByteArrayOutputStream out  = new ByteArrayOutputStream();

			do {
				try {
					n_replacements = proc.process(in_t, out);
				} catch (IOException e) {
					e.printStackTrace();
				}
				
				// Swap output to input
				in_t = new ByteArrayInputStream(out.toByteArray());
				out = new ByteArrayOutputStream();
			} while (n_replacements > 0);

			// Indent the new content if it is SystemVerilog
			InputStream in_ind = null;
			if (should_sv_indent(name)) {
				SVIndentScanner scanner = new SVIndentScanner(
						new InputStreamTextScanner(in_t, name));
				ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
				indenter.init(scanner);
				in_ind = new StringInputStream(indenter.indent());
			} else {
				in_ind = in_t;
			}

			fStreamProvider.createFile(name, in_ind);
			template.closeTemplate(in);
		}
		
		proc.removeParameterProvider(local_p);
	}
	
	private boolean should_sv_indent(String name) {
		String ext = "";
		
		if (name.lastIndexOf('.') != -1) {
			ext = name.substring(name.lastIndexOf('.'));
		}
		
		List<String> exts = SVCorePlugin.getDefault().getDefaultSVExts();
		return exts.contains(ext);
	}
	
	private ByteArrayInputStream readInputStream(InputStream in) {
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		byte tmp[] = new byte[16384];
		int len;
		
		try {
			while ((len = in.read(tmp, 0, tmp.length)) > 0) {
				bos.write(tmp, 0, len);
			}
		} catch (IOException e) {}
		
		return new ByteArrayInputStream(bos.toByteArray());
	}
	
}
