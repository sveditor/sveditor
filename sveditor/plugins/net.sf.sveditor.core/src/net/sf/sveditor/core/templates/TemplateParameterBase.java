package net.sf.sveditor.core.templates;

public class TemplateParameterBase {
	protected TemplateParameterType			fType;
	protected String						fName;
	protected String						fDescription;
	
	public TemplateParameterBase(TemplateParameterType type) {
		fType = type;
	}
	
	public TemplateParameterBase(TemplateParameterBase other) {
		fType = other.fType;
		fName = other.fName;
		fDescription = other.fDescription;
	}

	public TemplateParameterType getType() {
		return fType;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public String getDescription() {
		return fDescription;
	}
	
	public void setDescription(String desc) {
		fDescription = desc;
	}

	public TemplateParameterBase clone() {
		return new TemplateParameterBase(this);
	}
	
}
