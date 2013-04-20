package net.sf.sveditor.core.templates;

import java.util.ArrayList;
import java.util.List;

public class TemplateParameter extends TemplateParameterBase {
	private String							fDefault;
	private String							fValue;
	private String							fExtFrom;
	private List<String>					fValues;
	
	public TemplateParameter(
			TemplateParameterType		type,
			String						name,
			String						dflt,
			String						ext_from) {
		super(type);
		setName(name);
		fDefault 	= dflt;
		fValue		= dflt;
		fExtFrom	= ext_from;
		fValues		= new ArrayList<String>();
	}
	
	public TemplateParameter(TemplateParameter other) {
		super(other);
	
		fDefault = other.fDefault;
		fValue   = other.fValue;
		fExtFrom = other.fExtFrom;
		
		fValues = new ArrayList<String>();
		for (String v : other.fValues) {
			fValues.add(v);
		}
	}
	
	public String getTypeName() {
		switch (fType) {
			case ParameterType_Id: {
				if (fValues.size() == 0) {
					return "identifier";
				} else {
					return "choice";
				}
			}
			case ParameterType_Class: return "class"; 
			case ParameterType_Int: return "integer"; 
			default: return "unknown";
		}
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
	
	public TemplateParameter clone() {
		return new TemplateParameter(this);
	}
	
}

