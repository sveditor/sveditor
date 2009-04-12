package net.sf.sveditor.core.db.index;

public class SVDBPluginLibIndexFactory implements ISVDBIndexFactory {

	public ISVDBIndex createSVDBIndex(String base_location) {
		return new SVDBPluginLibIndex(base_location);
	}

}
