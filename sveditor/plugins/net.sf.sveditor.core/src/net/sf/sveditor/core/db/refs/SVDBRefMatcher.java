package net.sf.sveditor.core.db.refs;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBLocation;

/**
 * Reference matcher driven by a reference finder. The task of 
 * this class is to match references found by the finder against
 * the spec.
 * 
 * @author ballance
 *
 */
public class SVDBRefMatcher implements ISVDBRefFinderVisitor {
	private ISVDBRefSearchSpec		fRefSpec;
	/*
	private SVDBRefType				fRefType;
	private String					fRefName;
	 */
	ISVDBRefVisitor					fRefCollector;
	
	public SVDBRefMatcher(
			ISVDBRefSearchSpec	ref_spec,
			ISVDBRefVisitor		ref_visitor) {
		fRefSpec = ref_spec;
		fRefCollector = ref_visitor;
	}

	/*
	public SVDBRefMatcher(
			SVDBRefType			ref_type,
			String				ref_name,
			ISVDBRefVisitor		ref_visitor) {
		fRefType = ref_type;
		fRefName = ref_name;
	}
	 */
	
	/*
	public List<SVDBRefItem> find_refs(SVDBFile file) {
		visitFile(file);
		return fRefList;
	}
	 */

	public void visitRef(
			long		 			loc,
			SVDBRefType 			type,
			Stack<ISVDBItemBase>	scope,
			String 					name) {
		if (fRefSpec.matches(loc, type, scope, name)) {
			List<ISVDBItemBase> ref_path = new ArrayList<ISVDBItemBase>();
			ref_path.addAll(scope);
			SVDBRefItem ref = new SVDBRefItem(ref_path, name, type);
			fRefCollector.visitRef(fRefSpec, ref);
		}
	}
}
