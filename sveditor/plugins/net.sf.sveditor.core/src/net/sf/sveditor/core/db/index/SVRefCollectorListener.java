package net.sf.sveditor.core.db.index;

import java.util.Set;

import net.sf.sveditor.core.parser.ISVTokenListener;
import net.sf.sveditor.core.parser.SVToken;

public class SVRefCollectorListener implements ISVTokenListener {
	private Set<String>				fRefSet;
	
	public SVRefCollectorListener(Set<String> ref_set) {
		fRefSet = ref_set;
		fRefSet.clear();
	}

	@Override
	public void tokenConsumed(SVToken tok) {
		if (tok.isIdentifier()) {
			fRefSet.add(tok.getImage());
		}
	}

	@Override
	public void ungetToken(SVToken tok) { }

}
