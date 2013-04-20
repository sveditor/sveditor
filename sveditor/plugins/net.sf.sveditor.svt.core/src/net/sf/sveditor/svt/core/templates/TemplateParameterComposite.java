package net.sf.sveditor.core.templates;

import java.util.ArrayList;
import java.util.List;

public class TemplateParameterComposite extends TemplateParameterBase {
	private List<TemplateParameterBase>			fParameters;
	private String								fDefinitionType;
	
	public TemplateParameterComposite() {
		super(TemplateParameterType.ParameterType_Composite);
		fParameters = new ArrayList<TemplateParameterBase>();
	}
	
	public TemplateParameterComposite(TemplateParameterComposite other) {
		super(other);
		
		fDefinitionType = other.fDefinitionType;
		
		fParameters = new ArrayList<TemplateParameterBase>();
		
		for (TemplateParameterBase p : other.fParameters) {
			fParameters.add(p.clone());
		}
	}
	
	public void setDefinitionType(String type) {
		fDefinitionType = type;
	}
	
	public String getDefinitionType() {
		return fDefinitionType;
	}
	
	public List<TemplateParameterBase> getParameters() {
		return fParameters;
	}
	
	public void addParameter(TemplateParameterBase p) {
		fParameters.add(p);
	}
	
	public TemplateParameterComposite clone() {
		return new TemplateParameterComposite(this);
	}

}
