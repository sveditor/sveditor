package net.sf.sveditor.core.db;

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
	public static Map<String, SVDBFileTree> organizeFiles(List<SVDBFile> files) {
		Map<String, SVDBFileTree> file_map = new HashMap<String, SVDBFileTree>();
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

		/** Do not need to remove the sub-files from the list
		for (int i=0; i<org_files.size(); i++) {
			SVDBFileTree f = org_files.get(i);
			
			if (f.getIncludedByFiles().size() == 1) {
				org_files.remove(f);
				i--;
			}
		}
		 */
		
		/**
		for (SVDBFileTree file_t : org_files) {
			
			if (file_t.getIncludedByFiles().size() > 1) {
				System.out.println("File " + file_t.getFilePath()+ 
						" is included by " + file_t.getIncludedByFiles().size() + " files");
			} else if (file_t.getIncludedByFiles().size() == 0) {
			} else if (file_t.getIncludedByFiles().size() == 1) {
				System.out.println("File " + file_t.getFilePath()+ 
						" is included by 1 file");
			}
		}
        */

		/*
		SVDBFileTree f = file_map.get(
				"/media/disk1/usr1/work/inFact/demos/uart_ovm_testbench_trunk/testbench_ovm/ovm-2.0.1/src/tlm/tlm_ifs.svh");
		
		if (f != null) {
			System.out.println("f includes: " + f.getIncludedFiles().size());
			while (f.getIncludedByFiles().size() == 1) {
				f = f.getIncludedByFiles().get(0);
				System.out.println("    included by \"" + f.getFilePath() + "\"");
			}
		}
		 */
		
		return file_map;
	}
	
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
				SVDBFileTree t = new SVDBFileTree(it.getName());
				file_t.getIncludedFiles().add(t);
			} else if (it instanceof SVDBPackageDecl) {
				for (SVDBItem it_p : ((SVDBPackageDecl) it).getItems()) {
					if (it_p instanceof SVDBInclude) {
						SVDBFileTree t = new SVDBFileTree(it.getName());
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
			boolean found = false;

			if (f.getSVDBFile() == null) {
				// Search the top-level list
				for (SVDBFileTree ft : files) {
					if (ft.getFilePath().endsWith(f.getFilePath())) {
						file_t.getIncludedFiles().set(i, ft);
						found = true;
						break;
					}
				}
				
				if (!found) {
					System.out.println("Could not resolve inc \"" + 
							f.getFilePath() + "\"");
				}
			}
		}
	}

	private static void resolveIncludedRefs(
			SVDBFileTree 		file_t, 
			List<SVDBFileTree> 	files) {
		for (SVDBFileTree f : files) {
			for (SVDBFileTree fi : f.getIncludedFiles()) {
				if (fi.equals(file_t)) {
					if (!file_t.getIncludedByFiles().contains(f)) {
						file_t.getIncludedByFiles().add(f);
					}
				}
			}
		}
	}

}
