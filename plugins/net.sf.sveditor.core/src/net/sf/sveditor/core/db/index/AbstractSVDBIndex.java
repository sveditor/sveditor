package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;

public abstract class AbstractSVDBIndex implements ISVDBIndex {
	protected String						fProjectName;
	protected Map<String, SVDBFile>			fFileIndex;
	protected boolean						fFileIndexValid;

	protected Map<String, SVDBFile>			fFileList;
	protected boolean						fFileListValid;

	protected ISVDBIncludeFileProvider		fIncludeFileProvider;

	protected ISVDBIndexRegistry			fIndexRegistry;
	
	protected static Pattern				fWinPathPattern;
	protected static final List<String>		fSVExtensions;
	protected static final List<String>		fIgnoreDirs;
	
	static {
		fSVExtensions = new ArrayList<String>();
		
		fSVExtensions.add(".sv");
		fSVExtensions.add(".svh");
		fSVExtensions.add(".v");
		fSVExtensions.add(".V");
		fSVExtensions.add(".vl");
		fSVExtensions.add(".vlog");
		
		fIgnoreDirs = new ArrayList<String>();
		fIgnoreDirs.add("/.svn/");
		fIgnoreDirs.add("/CVS/");
		
		fWinPathPattern = Pattern.compile("\\\\");
	}

	public AbstractSVDBIndex(String project) {
		fProjectName = project;
		
		fFileList = new HashMap<String, SVDBFile>();
		fFileIndex = new HashMap<String, SVDBFile>();
		
	}

	public void init(ISVDBIndexRegistry registry) {
		fIndexRegistry = registry;
	}

	public void setIncludeFileProvider(ISVDBIncludeFileProvider provider) {
		fIncludeFileProvider = provider;
	}

	public boolean isLoaded() {
		return (fFileIndexValid && fFileListValid);
	}
	
	/**
	 * Search for an include file locally
	 */
	public SVDBFile findIncludedFile(String leaf) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		
		Iterator<String> it = map.keySet().iterator();
		
		while (it.hasNext()) {
			String f = it.next();
			
			String norm_path = fWinPathPattern.matcher(f).replaceAll("/");
			
			if (norm_path.endsWith(leaf)) {
				return map.get(f);
			}
		}
		
		return null;
	}
	
	public SVDBFile findIncludedFileGlobal(String leaf) {
		SVDBFile ret = findIncludedFile(leaf);
		
		if (ret != null && fIncludeFileProvider != null) {
			ret = fIncludeFileProvider.findIncludedFile(leaf);
		}
		
		return ret;
	}

	public void load(List<SVDBFile> pp_files, List<SVDBFile> db_files) {
		System.out.println("AbstractSVDBIndex.load()");
		
		fFileList.clear();
		fFileIndex.clear();
		
		for (SVDBFile f : pp_files) {
			fFileList.put(f.getFilePath(), f);
		}
		
		for (SVDBFile f : db_files) {
			fFileIndex.put(f.getFilePath(), f);
		}

		if (isLoadUpToDate()) {
			System.out.println("[NOTE] index \"" + getBaseLocation() + "\" IS up-to-date");
			fFileIndexValid = true;
			fFileListValid  = true;
		} else {
			System.out.println("[NOTE] index \"" + getBaseLocation() + "\" NOT up-to-date");
			fFileIndexValid = false;
			fFileListValid  = false;
			fFileList.clear();
			fFileIndex.clear();
		}
	}
	
	protected abstract boolean isLoadUpToDate();

	public synchronized Map<String, SVDBFile> getFileDB() {
		if (!fFileIndexValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fFileIndexValid) {
			buildIndex();
		}
		
		return fFileIndex;
	}

	protected abstract void buildIndex();

	public synchronized Map<String, SVDBFile> getPreProcFileMap() {
		if (!fFileListValid && fIndexRegistry != null) {
			fIndexRegistry.loadPersistedData(fProjectName, this);
		}
		
		if (!fFileListValid) {
			buildPreProcFileMap();
		}
		
		return fFileList;
	}

	protected abstract void buildPreProcFileMap();

	public ISVDBItemIterator<SVDBItem> getItemIterator() {
		return new SVDBIndexItemIterator(getFileDB());
	}
	
	public SVDBFile findFile(String path) {
		Map<String, SVDBFile> map = getFileDB();
		
		return map.get(path);
	}

	public SVDBFile findPreProcFile(String path) {
		Map<String, SVDBFile> map = getPreProcFileMap();
		return map.get(path);
	}
	

	public void dispose() {
	}
	
	protected static String expandVars(
			String 			path,
			boolean			expand_env_vars) {
		boolean workspace_prefix = path.startsWith("${workspace_loc}");
		String exp_path = path;
		
		if (workspace_prefix) {
			exp_path = exp_path.substring("${workspace_loc}".length());
		}
		
		IStringVariableManager mgr = VariablesPlugin.getDefault().getStringVariableManager();
		
		try {
			exp_path = mgr.performStringSubstitution(exp_path);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		if (expand_env_vars) {
			StringBuilder sb = new StringBuilder(exp_path);
			StringBuilder tmp = new StringBuilder();
			int idx = 0;
			
			while (idx < sb.length()) {
				if (sb.charAt(idx) == '$') {
					tmp.setLength(0);
					
					int start = idx, end;
					String key, val=null;
					idx++;
					if (sb.charAt(idx) == '{') {
						idx++;
						
						while (idx < sb.length() && sb.charAt(idx) != '}') {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						end = idx;
					} else {
						while (idx < sb.length() && 
								sb.charAt(idx) != '/' && !Character.isWhitespace(sb.charAt(idx))) {
							tmp.append(sb.charAt(idx));
							idx++;
						}
						end = (idx-1);
					}

					key = tmp.toString();
					if ((val = System.getenv(key)) != null) {
						sb.replace(start, end, val);
					}
				} else {
					idx++;
				}
			}
			
			for (int i=0; i<sb.length(); i++) {
				
			}
		}
		
		if (workspace_prefix) {
			exp_path = "${workspace_loc}" + exp_path;
		}
		
		return exp_path;
	}
	
}
