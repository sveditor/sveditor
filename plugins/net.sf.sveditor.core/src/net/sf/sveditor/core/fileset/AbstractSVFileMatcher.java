package net.sf.sveditor.core.fileset;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public abstract class AbstractSVFileMatcher {
	protected static Pattern				fNormalizePathPattern;
	protected boolean						fPatternsValid;
	protected List<Pattern>					fIncludePatterns;
	protected List<Pattern>					fExcludePatterns;
	protected List<SVFileSet>				fFileSets;

	// Pattern to normalize a Windows path to a UNC-style path
	static {
		fNormalizePathPattern = Pattern.compile("\\\\");
	}
	
	public AbstractSVFileMatcher() {
		fIncludePatterns 	= new ArrayList<Pattern>();
		
		fExcludePatterns 	= new ArrayList<Pattern>();
		fFileSets			= new ArrayList<SVFileSet>();
		fPatternsValid = false;
	}
	
	public void addFileSet(SVFileSet fs) {
		fFileSets.add(fs);
		fPatternsValid = false;
	}
	
	public abstract List<String> findIncludedPaths();

	/**
	 * include_file
	 * 
	 * @param path
	 * @return
	 */
	protected boolean include_file(String path) {
		// Normalize the path before doing matching 
		path = fNormalizePathPattern.matcher(path).replaceAll("/");
		
		if (!fPatternsValid) {
			update_patterns();
			fPatternsValid = true;
		}
		
		boolean include = (fIncludePatterns.size() == 0);
		
		// Check whether this file is included
		for (Pattern p : fIncludePatterns) {
			Matcher m = p.matcher(path);
			
			if (m.matches()) {
				include = true;
				break;
			}
		}
		
		if (include) {
			// Now, check whether this file is excluded
			boolean exclude = false;
			
			for (Pattern p : fExcludePatterns) {
				Matcher m = p.matcher(path);
				
				if (m.matches()) {
					exclude = true;
					break;
				}
			}
			
			return !exclude;
		} else {
			return false;
		}
	}
	protected void update_patterns() {
		StringBuilder p_s = new StringBuilder();
		fIncludePatterns.clear();
		fExcludePatterns.clear();

		for (SVFileSet fs : fFileSets) {
			for (String inc : fs.getIncludes()) {
				create_regexp(inc, p_s);

				// System.out.println("Include pattern \"" + inc + "\" => \"" + p_s.toString() + "\"");
				fIncludePatterns.add(Pattern.compile(p_s.toString()));

				// TODO: create include pattern from include
			}

			for (String exc : fs.getExcludes()) {
				create_regexp(exc, p_s);

				fExcludePatterns.add(Pattern.compile(p_s.toString()));
			}
		}
	}
	
	private static void create_regexp(
			String				pattern,
			StringBuilder		regexp) {
		regexp.setLength(0);
		
		// If the pattern doesn't contain any path separators, then
		// we have a file pattern
		regexp.append(".*");
		
		for (int i=0; i<pattern.length(); i++) {
			char ch = pattern.charAt(i);
			
			if (ch == '.') {
				regexp.append("\\.");
			} else if (ch == '*') {
				if (i+1 >= pattern.length() || pattern.charAt(i+1) != '*') {
					// Only a single '*'
					regexp.append("[^/]*");
				} else {
					// Double '**'
					// This is a directory wildcard
					regexp.append("([^/]+/)*");
				}
			} else {
				regexp.append(ch);
			}
		}
	}
}

