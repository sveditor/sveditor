package net.sf.sveditor.svt.core.templates;

import java.text.SimpleDateFormat;
import java.util.Date;

public class DynamicTemplateParameterProvider implements
		ITemplateParameterProvider {

	public boolean providesParameter(String id) {
		return (id.equals("date") || id.equals("user"));
	}

	public String getParameterValue(String id, String arg) {
		if (id.equals("user")) {
			return System.getProperty("user.name");
		} else if (id.equals("date")) {
			SimpleDateFormat format;
			if (arg != null) {
				format = new SimpleDateFormat(arg);
			} else {
				format = new SimpleDateFormat("MM/dd/YYYY");
			}
			return format.format(new Date());
		} else {
			return null;
		}
	}

}
