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


package net.sf.sveditor.core.fileset;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;

public class SVWorkspaceFileMatcher extends AbstractSVFileMatcher {
	
	public SVWorkspaceFileMatcher() {
		fLog = LogFactory.getLogHandle("SVWorkspaceFileMatcher");
	}
	
	@Override
	public List<String> findIncludedPaths() {
		final List<String> ret = new ArrayList<String>();
		
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		
		for (SVFileSet fs : fFileSets) {
			String base_location = fs.getBase();
			
			if (base_location.startsWith("${workspace_loc}")) {
				base_location = base_location.substring("${workspace_loc}".length());
			}
			
			try {
				IResource base = root.findMember(base_location);
				
				if (base == null) {
					fLog.error("Base Location \"" + base_location + "\" does not exist");
					continue;
				}
				if (!(base instanceof IContainer)) {
					fLog.error("Base Location \"" + base_location + "\" is not a folder");
					continue;
				}
				
				base.refreshLocal(IResource.DEPTH_INFINITE, null);
				IContainer c = (IContainer)base;
				
				recurse(c, ret);
			} catch (CoreException e) { }
		}
		
		return ret;
	}
	
	private void recurse(IContainer parent, List<String> paths) throws CoreException {
		IResource member_l[] = parent.members();
		
		if (member_l != null) {
			for (IResource m : member_l) {
				String full_path = m.getFullPath().toPortableString();
				if (m instanceof IContainer) {
					if (include_dir(full_path)) {
						recurse((IContainer)m, paths);
					}
				} else {
					if (include_file(full_path)) {
						String path = "${workspace_loc}" + full_path; 
						if (!paths.contains(path)) {
							paths.add(path);
						}
					}
				}
			}
		}
	}
}
