package net.sf.sveditor.ui.explorer;

import java.util.Collection;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;

public class PathTreeNodeFactory {
	
	public List<PathTreeNode> build(Collection<SVDBFile> file_set) {
		PathTreeNode root = new PathTreeNode("ROOT");
		
		for (SVDBFile file : file_set) {
			insert_file(root, file);
		}
		
		collapse_tree(root);

		return root.getChildNodes();
	}
	
	private void insert_file(PathTreeNode root, SVDBFile file) {
		String path = SVFileUtils.normalize(file.getFilePath());
		PathTreeNode curr = root;
		StringBuilder path_elem = new StringBuilder();
		int idx=0;

		while (idx < path.length() && path.charAt(idx) == '/') {
			idx++;
		}

		while (idx < path.length()) {
			
			path_elem.setLength(0);
			while (idx < path.length() && path.charAt(idx) != '/') {
				path_elem.append(path.charAt(idx));
				idx++;
			}

			// trim any trailing slashes so we can tell whether 
			// this is a leaf or not
			while (idx < path.length() && path.charAt(idx) == '/') {
				idx++;
			}
			
			String path_elem_s = path_elem.toString();
			
			if (path_elem_s.length() > 0) {
				if (idx < path.length()) {
					// insert a new node
					PathTreeNode n = null;
					for (PathTreeNode t : curr.getChildNodes()) {
						if (t.getName().equals(path_elem_s)) {
							n = t;
							break;
						}
					}
					if (n == null) {
						n = new PathTreeNode(path_elem_s);
						curr.getChildNodes().add(n);
					}
					curr = n;
				} else {
					curr.getFileList().add(file);
				}
			}
		}
	}
	
	private void collapse_tree(PathTreeNode root) {
		StringBuilder path_s = new StringBuilder();
		
		for (int i=0; i<root.getChildNodes().size(); i++) {
			PathTreeNode c = root.getChildNodes().get(i);

			path_s.setLength(0);

			if (c.getChildNodes().size() == 1) {
				PathTreeNode this_phase_root = c;
				
				// TODO: handle Windows paths
				if (c.getName().length() >= 2 && 
						((c.getName().charAt(0) >= 'a' && c.getName().charAt(0) <= 'z') ||
								(c.getName().charAt(0) >= 'A' && c.getName().charAt(0) <= 'Z')) &&
								c.getName().charAt(1) == ':') {
					path_s.append(c.getName());
				} else {
					path_s.append("/");
					path_s.append(c.getName());
				}
				
				c = c.getChildNodes().get(0);
				
				// TODO: should try to collapse lower portions of the tree as well (?)

				while (c.getChildNodes().size() == 1 &&
						c.getFileList().size() == 0) {
					path_s.append("/");
					path_s.append(c.getName());
					
					if (c.getChildNodes().size() == 1) {
						c = c.getChildNodes().get(0);
					} else {
						break;
					}
				}
				
				// Okay, now we have a root path. Update the original child node 
				
				// If where we landed only has SVDBFile entries, then copy them up.
				// Otherwise,
				this_phase_root.setName(path_s.toString());
				if (c.getChildNodes().size() == 0) {
					this_phase_root.getFileList().addAll(c.getFileList());
				} else {
					this_phase_root.getChildNodes().clear();
					this_phase_root.getChildNodes().addAll(c.getChildNodes());
					this_phase_root.getFileList().addAll(c.getFileList());
				}
			}
		}
	}
}
