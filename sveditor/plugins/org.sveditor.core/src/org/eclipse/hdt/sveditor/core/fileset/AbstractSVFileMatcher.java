/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.fileset;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.log.LogHandle;


public abstract class AbstractSVFileMatcher {
	protected static Pattern				fNormalizePathPattern;
	protected boolean						fPatternsValid;
	protected List<FilePattern>				fIncludePatterns;
	protected List<FilePattern>				fExcludePatterns;
	protected List<SVFileSet>				fFileSets;
	protected LogHandle						fLog;
	
	private class FilePattern {
		public Pattern				fDirMatchPattern;
		public Pattern				fFileMatchPattern;
	}

	// Pattern to normalize a Windows path to a UNC-style path
	static {
		fNormalizePathPattern = Pattern.compile("\\\\");
	}
	
	public AbstractSVFileMatcher() {
		fIncludePatterns 	= new ArrayList<FilePattern>();
		
		fExcludePatterns 	= new ArrayList<FilePattern>();
		fFileSets			= new ArrayList<SVFileSet>();
		fPatternsValid = false;
	}
	
	public void addFileSet(SVFileSet fs) {
		fFileSets.add(fs);
		fPatternsValid = false;
	}
	
	public abstract List<String> findIncludedPaths();
	
	/*
	 * include_dir()
	 * 
	 * Returns true if the directory should be entered
	 */
	protected boolean include_dir(String path) {
		// Normalize the path before doing matching 
		path = fNormalizePathPattern.matcher(path).replaceAll("/");

		if (!fPatternsValid) {
			update_patterns();
			fPatternsValid = true;
		}
		
		boolean include = (fIncludePatterns.size() == 0);
		
		// Check whether this file is included
		for (FilePattern p : fIncludePatterns) {
			Matcher m = p.fDirMatchPattern.matcher(path);
			
			if (m.matches()) {
				include = true;
				break;
			}
		}
		
		if (include) {
			// Now, check whether this file is excluded
			boolean exclude = false;
			
			for (FilePattern p : fExcludePatterns) {
				Matcher m = p.fDirMatchPattern.matcher(path);
				
				if (m.matches()) {
					exclude = true;
					break;
				}
			}

			fLog.debug("Dir \"" + path + "\" " + ((exclude)?"not":"") + " included");

			return !exclude;
		} else {
			fLog.debug("Dir \"" + path + "\" not included");
			return false;
		}
	}

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
		for (FilePattern p : fIncludePatterns) {
			fLog.debug("Match file " + path + " against pattern " + p.fFileMatchPattern.pattern());
			Matcher m = p.fFileMatchPattern.matcher(path);
			
			if (m.matches()) {
				include = true;
				break;
			}
		}
		
		if (include) {
			// Now, check whether this file is excluded
			boolean exclude = false;
			
			for (FilePattern p : fExcludePatterns) {
				Matcher m = p.fFileMatchPattern.matcher(path);
				
				if (m.matches()) {
					exclude = true;
					break;
				}
			}
			
			fLog.debug("Path \"" + path + "\" " + ((exclude)?"not":"") + " included");
			return !exclude;
		} else {
			fLog.debug("Path \"" + path + "\" not included");
			return false;
		}
	}
	
	protected void update_patterns() {
		fIncludePatterns.clear();
		fExcludePatterns.clear();

		for (SVFileSet fs : fFileSets) {
			for (String inc : fs.getIncludes()) {
				try {
					fIncludePatterns.add(create_pattern(fs.getBase(), inc));
				} catch (PatternSyntaxException e) {
					fLog.error("Failed to compile base=" + fs.getBase() + " incl=" + inc, e);
				}
			}

			for (String exc : fs.getExcludes()) {
				try {
					FilePattern p = create_pattern(fs.getBase(), exc);
					fExcludePatterns.add(p);
				} catch (PatternSyntaxException e) {
					fLog.error("Failed to compile base=" + fs.getBase() + " excl=" + exc, e);
				}
			}
		}
	}
	
	private FilePattern create_pattern(String base, String pattern) {
		FilePattern p = new FilePattern();
		
		// We can't include ${workspace_loc} in the pattern. Besides, 
		// the match path will not include this either
		if (base.startsWith("${workspace_loc}")) {
			base = base.substring("${workspace_loc}".length());
		}
		base = SVFileUtils.normalize(base);
		
		// The actual pattern is:
		// <base> + <ext_dir_path> + <leaf>
		int last_slash = pattern.lastIndexOf("/");
		
		if (last_slash != -1) {
			// This is a pathed pattern
			String leaf = pattern.substring(last_slash+1);
			String ext_dir_path = pattern.substring(0, last_slash);
			p.fDirMatchPattern = Pattern.compile(create_regexp(
					base + "/" + ext_dir_path), Pattern.CASE_INSENSITIVE);
			p.fFileMatchPattern = Pattern.compile(create_regexp(
					base + "/" + ext_dir_path + leaf), Pattern.CASE_INSENSITIVE);
		} else {
			// Non-pathed pattern. Only search base+leaf
			p.fDirMatchPattern  = Pattern.compile(create_regexp(base), Pattern.CASE_INSENSITIVE);
			p.fFileMatchPattern = Pattern.compile(create_regexp(base + "/" + pattern), Pattern.CASE_INSENSITIVE); 
		}
		
		return p;
	}
	
	private static String create_regexp(String pattern) {
		StringBuilder regexp = new StringBuilder();
		regexp.setLength(0);
		
		// If the pattern doesn't contain any path separators, then
		// we have a file pattern
//		regexp.append(".*");
		
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
		
		return regexp.toString();
	}
}
