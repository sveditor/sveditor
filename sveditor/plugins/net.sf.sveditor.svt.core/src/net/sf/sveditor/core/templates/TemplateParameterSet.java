package net.sf.sveditor.core.templates;

import java.util.ArrayList;
import java.util.List;

public class TemplateParameterSet {
	private List<TemplateParameterBase>				fParameters;
	
	public TemplateParameterSet() {
		fParameters = new ArrayList<TemplateParameterBase>();
	}
	
	public List<TemplateParameterBase> getParameters() {
		return fParameters;
	}
	
	public List<TemplateParameterBase> getParametersFlat() {
		List<TemplateParameterBase> ret = new ArrayList<TemplateParameterBase>();
		
		for (TemplateParameterBase p : fParameters) {
			if (p.getType() == TemplateParameterType.ParameterType_Group) {
				collectGroupParams(ret, (TemplateParameterGroup)p);
			} else {
				ret.add(p);
			}
		}
		
		return ret;
	}
	
	private void collectGroupParams(List<TemplateParameterBase> params, TemplateParameterGroup group) {
		for (TemplateParameterBase p : group.getParameters()) {
			if (p.getType() == TemplateParameterType.ParameterType_Group) {
				collectGroupParams(params, (TemplateParameterGroup)p);
			} else {
				params.add(p);
			}
		}
	}
	
	public TemplateParameterProvider getParameterProvider() {
		TemplateParameterProvider tp = new TemplateParameterProvider();

		for (TemplateParameterBase p : getParametersFlat()) {
			if (p instanceof TemplateParameter) {
				tp.setTag(p.getName(), ((TemplateParameter)p).getValue());
			} else if (p.getType() == TemplateParameterType.ParameterType_Composite) {
				addCompositeParams(p.getName(), tp, (TemplateParameterComposite)p);
			}
		}
		
		return tp;		
	}
	
	private void addCompositeParams(String root, TemplateParameterProvider tp, TemplateParameterComposite p) {
		
		for (TemplateParameterBase ps : p.getParameters()) {
			if (ps instanceof TemplateParameter) {
				tp.setTag(root + "." + ps.getName(), ((TemplateParameter)ps).getValue());
			}
			
		}
	}
	
	public void addParameter(TemplateParameterBase param) {
		if (param == null) {
			try {
				throw new Exception("Null Parameter");
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		fParameters.add(param);
	}
	
	// TODO: findParameter

}
