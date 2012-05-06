package net.sf.sveditor.core.templates;

import java.util.ArrayList;
import java.util.List;

public class TemplateParameter {
	private TemplateParameterType			fType;
	private String							fName;
	private String							fDefault;
	private String							fValue;
	private String							fExtFrom;
	private List<String>					fValues;
	
	public TemplateParameter(
			TemplateParameterType		type,
			String						name,
			String						dflt,
			String						ext_from) {
		fType 		= type;
		fName 		= name;
		fDefault 	= dflt;
		fValue		= dflt;
		fExtFrom	= ext_from;
		fValues		= new ArrayList<String>();
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
	
	public String getValue() {
		return fValue;
	}
	
	public void setValue(String val) {
		fValue = val;
	}

	public String getExtFrom() {
		return fExtFrom;
	}
	
	public List<String> getValues() {
		return fValues;
	}
	
	public void addValue(String value) {
		if (!fValues.contains(value)) {
			fValues.add(value);
		}
	}
	
	public TemplateParameter duplicate() {
		TemplateParameter p = new TemplateParameter(fType, fName, fDefault, fExtFrom);
		p.setValue(fValue);
		
		for (String v : fValues) {
			p.addValue(v);
		}
		
		return p;
	}
}

