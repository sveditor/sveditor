package net.sf.sveditor.core.preproc;

import net.sf.sveditor.core.db.ISVDBItemBase;

public class SVPreProcEvent {
	public enum Type {
		BeginExpand,
		EndExpand,
		Define,
		EnterFile,
		LeaveFile
	};
	
	public SVPreProcEvent(SVPreProcEvent.Type t) {
		type = t;
	}
	
	public Type				type;
	public String			text;
	// Valid for EnterFile and LeaveFile
	public int				file_id;
	public int				pos;
	// Valid for Type.Define
	public ISVDBItemBase	decl;

}
