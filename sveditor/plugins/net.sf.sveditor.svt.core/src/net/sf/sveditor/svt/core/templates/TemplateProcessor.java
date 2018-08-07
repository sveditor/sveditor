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


package net.sf.sveditor.svt.core.templates;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javax.script.Invocable;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.tagproc.TagProcessor;
import net.sf.sveditor.core.tagproc.TemplateParameterProvider;

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
	
	private void runGenerateScript(
			InputStream 			in,
			TemplateInfo			template,
			TemplateParameterSet	parameters) throws ScriptException, NoSuchMethodException {
		ScriptEngineManager factory = new ScriptEngineManager();
		ScriptEngine engine = factory.getEngineByName("JavaScript");
		
		// Source script
		engine.eval(new InputStreamReader(in));
	
		try {
			in.close();
		} catch (IOException e) {}
	
		Invocable inv = (Invocable)engine;
		
		inv.invokeFunction("generate", template, parameters);
//		inv.invokeFunction("generate", args)
	}
	
	public void process(TemplateInfo template, TagProcessor proc) {
		TemplateParameterProvider local_p = new TemplateParameterProvider();
		proc.addParameterProvider(local_p);
		
		TemplateParameterSet parameters = new TemplateParameterSet();
	
		// TODO: This should probably be getParametersFlat()
		for (TemplateParameterBase p : template.getParameters().getParameters()) {
			parameters.addParameter(p.clone());
		}
		
		/*
		if (!proc.hasTag("file_header")) {
			proc.setTag("file_header", fDefaultFileHeader);
		}
		 */
		
		// TODO: Execute a JavaScript script if specified
		if (template.getGenerateScript() != null) {
			InputStream in = template.openTemplate(template.getGenerateScript());
			
			System.out.println(" IN: " + in);
			if (in != null) {
				try {
					runGenerateScript(in, template, parameters);
				} catch (ScriptException e) {
					e.printStackTrace();
				} catch (NoSuchMethodException e) {
					e.printStackTrace();
				}
				template.closeTemplate(in);
			}
		}
		
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

			fStreamProvider.createFile(name, in_ind, template.getExecutable(templ));
			template.closeTemplate(in);
		}
		
		proc.removeParameterProvider(local_p);
	}
	
	private boolean should_sv_indent(String name) {
		String ext = "";
		
		if (name.lastIndexOf('.') != -1) {
			ext = name.substring(name.lastIndexOf('.'));
		}
		
		Set<String> exts = SVCorePlugin.getDefault().getDefaultSVExts();
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
