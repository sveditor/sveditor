package net.sf.sveditor.core.evaluator;

public interface ISVEvalContext {
	
	ISVEvalContext getParent();
	
	void setParent(ISVEvalContext parent);

}
