package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SVDBFileTreeUtils {

	/**
	 * Given a list of SVDBFiles from the SVPreProcScanner, resolve the
	 * `include relationships between these files
	 * 
	 * @param files
	 */
	public static Map<File, SVDBFileTree> organizeFiles(List<SVDBFile> files) {
		Map<File, SVDBFileTree> file_map = new HashMap<File, SVDBFileTree>();
		List<SVDBFileTree> org_files = new ArrayList<SVDBFileTree>();
		
		for (SVDBFile f : files) {
			SVDBFileTree file_t = new SVDBFileTree(f);
			// Populate the includedFiles array
			setupIncludedFiles(file_t, f);
			org_files.add(file_t);
		}
		
		// Now, crawl through the list and resolve the inclusions
		for (SVDBFileTree file_t : org_files) {
			resolveInclusions(file_t, org_files);
		}
		
		// Next, revisit the list to setup lists of included references
		for (SVDBFileTree file_t : org_files) {
			resolveIncludedRefs(file_t, org_files);
		}
		
		for (SVDBFileTree file_t : org_files) {
			file_map.put(file_t.getFilePath(), file_t);
		}

		return file_map;
	}
	
	/*
	public static SVDBFileTree resolveInclusions(
			SVDBFileTree						file,
			List<Map<File, SVDBFileTree>>		file_maps) {
		
	}
	 */
					
			
	
	public static void updateFiles(
			Map<String, SVDBFileTree>	map,
			SVDBFile					new_file) {
		SVDBFileTree file_t = new SVDBFileTree(new_file);
		setupIncludedFiles(file_t, new_file);
	}
	
	private static void setupIncludedFiles(
			SVDBFileTree			file_t,
			SVDBFile				file) {
		for (SVDBItem it : file.getItems()) {
			if (it instanceof SVDBInclude) {
				SVDBFileTree t = new SVDBFileTree(new File(it.getName()));
				file_t.getIncludedFiles().add(t);
			} else if (it instanceof SVDBPackageDecl) {
				for (SVDBItem it_p : ((SVDBPackageDecl) it).getItems()) {
					if (it_p instanceof SVDBInclude) {
						SVDBFileTree t = new SVDBFileTree(new File(it_p.getName()));
						file_t.getIncludedFiles().add(t);
					}
				}
			}
		}
	}
	
	private static void resolveInclusions(
			SVDBFileTree 		file_t, 
			List<SVDBFileTree> 	files) {
		for (int i=0; i<file_t.getIncludedFiles().size(); i++) {
			SVDBFileTree f = file_t.getIncludedFiles().get(i);
			SVDBFileTree inc_file = null;

			if (f.getSVDBFile() == null) {
				// Search the top-level list
				for (SVDBFileTree ft : files) {
					// TODO: must account for other files with the same name
					// - Use distance as a similarity metric?
					if (ft.getFilePath().getPath().endsWith(f.getFilePath().getPath())) {
						if (inc_file != null) {
							inc_file = determineClosestMatch(file_t, f, inc_file, ft);
						} else {
							inc_file = ft;
						}
					}
				}
				
				if (inc_file != null) {
					file_t.getIncludedFiles().set(i, inc_file);
				} else {
					System.out.println("Could not resolve inc \"" + 
							f.getFilePath() + "\"");
				}
			}
		}
	}
	
	private static SVDBFileTree determineClosestMatch(
			SVDBFileTree		inc_file,
			SVDBFileTree		inc_path,
			SVDBFileTree		f1,
			SVDBFileTree		f2) {
		System.out.println("determineClosestMatc: include \"" + 
				inc_path.getFilePath() + "\" in file \"" + 
				inc_file.getFilePath() + "\"");
		System.out.println("    f1: " + f1.getFilePath());
		System.out.println("    f2: " + f2.getFilePath());
		
		return f1;
	}

	private static void resolveIncludedRefs(
			SVDBFileTree 		file_t, 
			List<SVDBFileTree> 	files) {
		for (SVDBFileTree f : files) {
			for (SVDBFileTree fi : f.getIncludedFiles()) {
				//if (fi.equals(file_t)) {
				if (fi.getFilePath().equals(file_t.getFilePath())) {
					if (!file_t.getIncludedByFiles().contains(f)) {
						file_t.getIncludedByFiles().add(f);
					}
				}
			}
		}
	}
}
