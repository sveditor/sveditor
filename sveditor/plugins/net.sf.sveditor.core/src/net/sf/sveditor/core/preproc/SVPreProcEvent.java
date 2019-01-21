package net.sf.sveditor.core.preproc;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFileTree;

public class SVPreProcEvent {
	public enum Type {
		BeginExpand,
		EndExpand,
		Define,
		MacroRef,
		EnterFile,
		LeaveFile,
		MissingInclude,
		Comment,
		Marker,
		Include
	};
	
	public SVPreProcEvent(SVPreProcEvent.Type t) {
		type = t;
	}
	
	public Type				type;
	public String			text;
	// Valid for EnterFile and LeaveFile
	public int				file_id;
	public int				pos;
	public long				loc;
	// Valid for Type.Define
	public ISVDBItemBase	decl;

	// TODO: back-compat for old indexes
	public SVDBFileTree		ft;

}
