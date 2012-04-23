package net.sf.sveditor.core.templates;

public class TemplateParameter {
	private TemplateParameterType			fType;
	private String							fName;
	private String							fDefault;
	private String							fExtFrom;
	
	public TemplateParameter(
			TemplateParameterType		type,
			String						name,
			String						dflt,
			String						ext_from) {
		fType 		= type;
		fName 		= name;
		fDefault 	= dflt;
		fExtFrom	= ext_from;
	}
	
	public TemplateParameterType getType() {
		return fType;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getDefault() {
		return fDefault;
	}

	public String getExtFrom() {
		return fExtFrom;
	}
}
