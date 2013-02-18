package net.sf.sveditor.core.preproc;

/**
 * SVEditor applies a File ID to each item within an index.
 * Implementations of the ISVPreProcFileMapper convert
 * a file path to a unique (on an index basis) id.
 * 
 * @author ballance
 *
 */
public interface ISVPreProcFileMapper {
	
	int mapFilePathToId(String path, boolean add);
	
	String mapFileIdToPath(int id);

}
