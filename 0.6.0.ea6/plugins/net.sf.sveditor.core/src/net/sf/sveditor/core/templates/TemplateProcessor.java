package net.sf.sveditor.core.templates;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.text.TagProcessor;

public class TemplateProcessor {
	private ITemplateOutStreamProvider			fStreamProvider;
	
	public TemplateProcessor(ITemplateOutStreamProvider provider) {
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
		for (Tuple<String, String> t : template.getTemplates()) {
			String templ = t.first();
			String name = proc.process(t.second());
			
			InputStream in = template.openTemplate(templ);
			OutputStream out = fStreamProvider.openStream(name);

			/*
			SVIndentScanner scanner = new SVIndentScanner(
					new StringTextScanner(content));
			ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
			indenter.init(scanner);
			final StringInputStream in = new StringInputStream(indenter.indent());
			 */
			
			try {
				proc.process(in, out);
			} catch (IOException e) {
				e.printStackTrace();
			}
			
			template.closeTemplate(in);
			fStreamProvider.closeStream(out);
		}
	}
	
}
