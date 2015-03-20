package net.sf.sveditor.core.tagproc;

public interface ITemplateParameterProvider {
	
	boolean providesParameter(String id);
	
	String getParameterValue(String id, String arg);

}
