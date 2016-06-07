package net.sf.sveditor.core.preproc;

public class PreProcEvent {
	public enum Type {
		BeginExpand,
		EndExpand
	};
	
	public PreProcEvent(PreProcEvent.Type t) {
		type = t;
	}
	
	public Type			type;
	public String		text;
	public int			pos;

}
