package net.sf.sveditor.core.methodology_templates;

import java.util.Map;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.indent.SVDefaultIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanutils.StringTextScanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class NewMethodologyClassGen {
	public static final String			KEY_CLASSNAME   = "classname";
	public static final String			KEY_SUPERCLASS  = "superclass";
	public static final String			KEY_FILENAME    = "filename";
	public static final String			KEY_FILENAME_ID = "filename_id";
	
	private MethodologyTemplate			fTemplate;
	private Map<String, String>			fParameters;
	
	public void generate(
			ISVDBIndexIterator			index_it,
			final IFile					file_path,
			MethodologyTemplate			template,
			Map<String, String>			parameters,
			IProgressMonitor			monitor) {
		fTemplate = template;
		fParameters = parameters;
		
		if (monitor == null) {
			monitor = new NullProgressMonitor();
		}
		monitor.beginTask("Creating class", 100);
		
		set_parameter(KEY_FILENAME, file_path.getName());
		set_parameter(KEY_FILENAME_ID, 
				SVCharacter.toSVIdentifier(file_path.getName()));
		
		String content = expand(template.getTemplate());
		
		// 
		
		monitor.subTask("Indenting content");
		SVIndentScanner scanner = new SVIndentScanner(
				new StringTextScanner(content));
		SVDefaultIndenter indenter = new SVDefaultIndenter();
		indenter.init(scanner);
		final StringInputStream in = new StringInputStream(indenter.indent());
		
		monitor.worked(25);
		
		try {
			if (file_path.exists()) {
				file_path.setContents(in, true, true, new NullProgressMonitor());
			} else {
				file_path.create(in, true, new NullProgressMonitor());
			}
		} catch (CoreException e) {}
		
		monitor.done();
	}
	
	private void set_parameter(String key, String val) {
		if (fParameters.containsKey(key)) {
			fParameters.remove(key);
		}
		if (val != null) {
			fParameters.put(key, val);
		}
	}
	
	private String expand(String in) {
		StringBuilder sb = new StringBuilder();
		StringBuilder var_tmp = new StringBuilder();
		
		int idx = 0;
		while (idx < in.length()) {
			if (in.charAt(idx) == '$' &&
					idx+1 < in.length() &&
					in.charAt(idx+1) == '{') {
				idx++; // skip {
				var_tmp.setLength(0);
				while (idx < in.length() && in.charAt(idx) != '}') {
					var_tmp.append(in.charAt(idx));
					idx++;
				}
				if (in.charAt(idx) == '}') {
					idx++;
					String key = var_tmp.toString();
					if (fParameters.containsKey(key)) {
						sb.append(fParameters.get(key));
					} else {
						// reference to a non-existent var
						sb.append("${");
						sb.append(var_tmp);
						sb.append("}");
					}
				} else {
					// not really a variable reference
					sb.append("${");
					sb.append(var_tmp);
				}
			} else {
				sb.append(in.charAt(idx));
			}
			idx++;
		}
		
		return sb.toString();
	}

}
