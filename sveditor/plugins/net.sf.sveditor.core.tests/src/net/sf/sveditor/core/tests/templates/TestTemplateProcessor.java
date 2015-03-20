package net.sf.sveditor.core.tests.templates;

import java.io.ByteArrayOutputStream;
import java.io.IOException;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.tagproc.ITemplateParameterProvider;
import net.sf.sveditor.core.tagproc.TagProcessor;

public class TestTemplateProcessor extends TestCase {
	
	public void testEmbeddedVariableRefs() {
		String input = 
				"$${VAR_NAME_SUBST} = $ENV{${VAR_NAME_SUBST}};";
		
		TagProcessor proc = new TagProcessor();
		proc.addParameterProvider(new ITemplateParameterProvider() {
			
			public boolean providesParameter(String id) {
				return (id.equals("VAR_NAME_SUBST"));
			}
			
			public String getParameterValue(String id, String arg) {
				if (id.equals("VAR_NAME_SUBST")) {
					return "MY_VAR";
				} else {
					return null;
				}
			}
		});
		
		StringInputStream in = new StringInputStream(input);
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		
		for (int i=0; i<4; i++) {
			int n_replacements = 0;
			try {
				n_replacements = proc.process(in, out);
			} catch (IOException e) {
				e.printStackTrace();
			}
		
			if (n_replacements > 0) {
				in = new StringInputStream(out.toString());
				out = new ByteArrayOutputStream();
			}
		}
		
		assertEquals("$MY_VAR = $ENV{MY_VAR};", out.toString());
	}

	public void testEmbeddedVariableRefs_2() {
		String input = 
				"${${VAR_NAME_SUBST}} = $(${VAR_NAME_SUBST});";
		
		TagProcessor proc = new TagProcessor();
		proc.addParameterProvider(new ITemplateParameterProvider() {
			
			public boolean providesParameter(String id) {
				return (id.equals("VAR_NAME_SUBST"));
			}
			
			public String getParameterValue(String id, String arg) {
				if (id.equals("VAR_NAME_SUBST")) {
					return "MY_VAR";
				} else {
					return null;
				}
			}
		});
		
		StringInputStream in = new StringInputStream(input);
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		
		for (int i=0; i<4; i++) {
			int n_replacements = 0;
			try {
				n_replacements = proc.process(in, out);
			} catch (IOException e) {
				e.printStackTrace();
			}
		
			if (n_replacements > 0) {
				in = new StringInputStream(out.toString());
				out = new ByteArrayOutputStream();
			}
		}
		
		assertEquals("${MY_VAR} = $(MY_VAR);", out.toString());
	}

}
