package net.sf.sveditor.core.templates;

public interface ITemplateParameterProvider {
	
	boolean providesParameter(String id);
	
	String getParameterValue(String id, String arg);

}
