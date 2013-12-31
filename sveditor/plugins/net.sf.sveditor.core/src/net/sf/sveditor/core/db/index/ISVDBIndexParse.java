package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;

import org.eclipse.core.runtime.IProgressMonitor;

/**
 * Implements the 'parseable' interface for ISVDBIndex
 * 
 * @author ballance
 *
 */
public interface ISVDBIndexParse {

	Tuple<SVDBFile, SVDBFile> parse(
			IProgressMonitor monitor,
			InputStream in, 
			String path, 
			List<SVDBMarker> markers);

	/**
	 * Creates a pre-processor for the specified path
	 * 
	 * @param path
	 * @return
	 */
	ISVStringPreProcessor createPreProc(
			String 				path,
			InputStream			in,
			int					limit_lineno);
}
