package net.sf.sveditor.core.tests.content_assist;

import java.io.InputStream;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

public class ContentAssistIndex extends AbstractSVDBIndex {
	
	public ContentAssistIndex() {
		super("GLOBAL");
	}
	
	public void setFile(SVDBFile file) {
		fFileIndex.remove(file.getName());
		fFileIndex.put(file.getName(), file);
	}

	@Override
	protected void buildIndex() {
		fFileIndexValid = true;
	}

	@Override
	protected void buildPreProcFileMap() {
		fFileListValid = true;
	}

	@Override
	protected boolean isLoadUpToDate() {
		return true;
	}

	public void addChangeListener(ISVDBIndexChangeListener l) {}

	public String getBaseLocation() {
		return "";
	}

	public int getIndexType() {
		return 0;
	}

	public String getTypeID() {
		return "ContentAssistIndex";
	}

	public void rebuildIndex() {}

	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	public SVDBFile parse(InputStream in, String path) {
		return null;
	}

	public SVDBSearchResult<SVDBFile> findIncludedFile(String leaf) {
		return null;
	}

}
