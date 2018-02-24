package net.sf.sveditor.core.preproc;

import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBUnprocessedRegion;

public class SVPreProc2InputData {

	private SVPreProcessor		fPreProc;
	private SVPreProcEvent		fBeginEv;
	private InputStream 		fInput;
	private String 				fFilename;
	private int 				fFileId;
	private int 				fLineno;
	private int 				fLinepos;
	private int 				fLineCount;
	private int 				fLastCh;
	private int 				fUngetCh1;
	private int 				fUngetCh2;
	private boolean 			fIncPos;
	private Map<String, String> fRefMacros;
	private SVDBUnprocessedRegion fUnprocessedRegion;

	SVPreProc2InputData(
			SVPreProcessor		preproc,
			InputStream 		in, 
			String 				filename, 
			int 				file_id) {
		this(preproc, in, filename, file_id, true);
	}
	
	SVPreProc2InputData(
			SVPreProcessor		preproc,
			InputStream 		in, 
			String 				filename, 
			int 				file_id, 
			boolean 			inc_pos) {
		fPreProc = preproc;
		fLineno = 1;
		fInput = in;
		fFilename = filename;
		fFileId   = file_id;
		fLastCh = -1;
		fIncPos = inc_pos;
		fRefMacros = new HashMap<String, String>();
		fUngetCh1 = -1;
		fUngetCh2 = -1;
	}
	
	public SVPreProcEvent getBeginEv() {
		return fBeginEv;
	}
	
	public void setBeginEv(SVPreProcEvent ev) {
		fBeginEv = ev;
	}
	
	public boolean incPos() {
		return fIncPos;
	}
	
	int get_ch() {
		int ch = -1;
		
		if (fUngetCh1 != -1) {
			ch = fUngetCh1;
			fUngetCh1 = fUngetCh2;
			fUngetCh2 = -1;
		
			if (fIncPos) {
				if (fLastCh == '\n') {
					fLineno++;
					fLineCount++;
				}
			}
			fLastCh = -1;
		} else {
			try {
				ch = fInput.read();
			} catch (IOException e) {}
			
			if (ch != -1) {
				if (fLastCh == '\n') {
					if (fIncPos) {
						// Save a marker for the line in the line map
						fLineno++;
						if (fPreProc != null) {
							fPreProc.add_file_change_info(fFileId, fLineno);
						}
					}
					fLineCount++;
				}
				fLastCh = ch;
			} else {
				// Handle the case where a file doesn't end with a newline
				// Just go ahead and ensure that every file does
				if (fLastCh != -1 && fLastCh != '\n') {
					// Only do this for real files
					if (!fFilename.startsWith("Macro:")) {
						ch = '\n';
					}
				}
				fLastCh = -1;
			}
		}
		
		return ch;
	}
	
	void unget_ch(int ch) {
		if (fUngetCh1 == -1) {
			fUngetCh1 = ch;
		} else {
			fUngetCh2 = fUngetCh1;
			fUngetCh1 = ch;
		}
	}
	
	InputStream getInput() {
		return fInput;
	}
	
	int getFileId() {
		return fFileId;
	}
	
	int getLineNo() {
		return fLineno;
	}
	
	String getFileName() {
		return fFilename;
	}
	
	int getLineCount() {
		return fLineCount;
	}
	
	void close() {
		try {
			if (fInput != null) {
				fInput.close();
			}
		} catch (IOException e) {}
	}
	
	long getLocation() {
		return SVDBLocation.pack(fFileId, fLineno, fLinepos);
	}
	
	void addRefMacro(String name, SVDBMacroDef m) {
		fRefMacros.remove(name);
		if (m == null) {
			fRefMacros.put(name, null);
		} else {
			fRefMacros.put(name, m.getDef());
		}		
	}
	
	void update_unprocessed_region(long loc, boolean enabled_pre, boolean enabled_post) {
		if (enabled_pre && !enabled_post) {
			// Entering an unprocessed region
			fUnprocessedRegion = new SVDBUnprocessedRegion();
			fUnprocessedRegion.setLocation(loc);
		} else if (!enabled_pre && enabled_post) {
			// Leaving an unprocessed region
			SVDBUnprocessedRegion r = fUnprocessedRegion;
			fUnprocessedRegion = null;

			System.out.println("TODO: update unprocessed region");
//			if (r != null && fFileTree != null) {
//				r.setEndLocation(loc);
//				fFileTree.getSVDBFile().addChildItem(r);
//			}
		}		
	}
	
	void leave_file() {
		if (fUnprocessedRegion != null) {
			// TODO: mark error
			// we fell off the end of the file with an ifdef active
			fUnprocessedRegion.setEndLocation(getLocation());
			System.out.println("TODO: update unprocessed region");
//			if (fFileTree != null) {
//				fFileTree.getSVDBFile().addChildItem(fUnprocessedRegion);
//			}
		}
		
		close();
	}
}
