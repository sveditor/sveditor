package net.sf.sveditor.ui.search;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

import org.eclipse.search.ui.text.Match;

public class SVSearchMatch extends Match {
	private SVDBFile				fFile;
	
	public SVSearchMatch(SVDBItem item) {
		super(item, 0, 0);
	}
	
	public SVDBFile getFile() {
		if (fFile == null) {
			SVDBItem it = (SVDBItem)getElement();
			while (it != null) {
				if (it.getType() == SVDBItemType.File) {
					fFile = (SVDBFile)it;
					break;
				}
				it = (SVDBItem)it.getParent();
			}
		}
		return fFile;
	}
}
