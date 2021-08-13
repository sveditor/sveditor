/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.applications;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;

public class CreateProjectApp implements IApplication {

	@Override
	public Object start(IApplicationContext context) throws Exception {
		String args[] = (String [])context.getArguments().get(IApplicationContext.APPLICATION_ARGS);
		String dir = null;
		List<String> argfiles = new ArrayList<String>();
		String name = null;
		
		for (int i=0; i<args.length; i++) {
			String arg = args[i];
			
			if (arg.charAt(0) == '-') {
				// Option
				if (arg.equals("-f")) {
					argfiles.add(args[++i]);
				} else if (arg.equals("-h") || arg.equals("-help") ||
						arg.equals("--help")) {
					printHelp();
					return Status.OK_STATUS;
				} else if (arg.equals("-name")) {
					name = args[++i];
				} else {
					fatal("Unknown option \"" + arg + "\"");
				}
			} else {
				if (dir != null) {
					fatal("Unknown argument \"" + dir + "\"");
				} else {
					dir = arg;
				}
			}
		}
		
		if (dir == null) {
			fatal("project directory not specified");
		}
		
		File dir_f = new File(dir);
		
		if (dir_f.isFile()) {
			fatal("Specified project directory \"" + dir + "\" is a file");
		}
		
		if (!dir_f.exists()) {
			System.out.println("Note: creating new project in empty directory \"" + dir + "\"");
			if (!dir_f.mkdirs()) {
				fatal("Failed to create directory \"" + dir + "\"");
			}
		}
	
		if (name == null) {
			name = dir_f.getName();
		}
		
		System.out.println("Note: Creating project in directory \"" + dir_f.getAbsolutePath() + "\"");
		
		IWorkspace ws = ResourcesPlugin.getWorkspace();
		
		IProject project = ws.getRoot().getProject(name);
	
		try {
			System.out.println("Note: a project named \"" + name + "\" already is in the workspace -- closing");
			if (project.exists()) {
				project.close(new NullProgressMonitor());
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		try {
			if (project.exists()) {
				project.delete(true, true, new NullProgressMonitor());
			}
		} catch (CoreException e) {
			e.printStackTrace();
		}
	
		try {
			IProjectDescription desc = ws.newProjectDescription(name);
			desc.setLocationURI(dir_f.toURI());
			
			String old_ids[] = desc.getNatureIds();
			String new_ids[] = new String[old_ids.length+1];
			
			System.arraycopy(old_ids, 0, new_ids, 0, 
					old_ids.length);
		
			new_ids[old_ids.length] = 
				SVCorePlugin.PLUGIN_ID + ".SVNature";
			
			desc.setNatureIds(new_ids);			
			
			project.create(desc, new NullProgressMonitor());
			
			// Now we must open the project
			if (!project.isOpen()) {
				project.open(new NullProgressMonitor());
			}
			
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			
			SVDBProjectData pdata = pmgr.getProjectData(project);
			SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
			fw.getArgFilePaths().clear();
			for (String argfile : argfiles) {
				// Need to form a project-relative path
				String proj_path = argfile;
				
				fw.addArgFilePath(proj_path);
			}
			pdata.setProjectFileWrapper(fw);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		return Status.OK_STATUS;
	}
	
	private void printHelp() {
		System.out.println("org.eclipse.hdt.sveditor.create_project [options] <project_path>");
		System.out.println("Options:");
		System.out.println("  -f <argument_file>     - Adds the specified argument file to the project");
		System.out.println("  -name <name>           - Specifies the project name");
	}
	
	private void fatal(String msg) throws Exception {
		System.out.println("Fatal: " + msg);
		printHelp();
		throw new Exception(msg);
	}

	@Override
	public void stop() {
		// TODO Auto-generated method stub

	}

}
