package net.sf.sveditor.core.db.index;

public interface ISVDBDeclCacheFileAttr {

	int							FILE_ATTR_HAS_MARKERS	= (1 << 0);
	// 
	int							FILE_ATTR_SRC_FILE		= (1 << 1);
	int							FILE_ATTR_ARG_FILE		= (1 << 2);
	// Passing ROOT_FILE causes only root files to be returned
	int							FILE_ATTR_ROOT_FILE		= (1 << 3);
	int							FILE_ATTR_LIB_FILE		= (1 << 4);
}
