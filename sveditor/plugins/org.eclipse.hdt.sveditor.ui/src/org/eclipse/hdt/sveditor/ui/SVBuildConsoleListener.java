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
package net.sf.sveditor.ui;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.builder.ISVBuilderOutputListener;
import org.eclipse.swt.widgets.Display;

import net.sf.sveditor.ui.console.SVConsole;
import net.sf.sveditor.ui.console.SVEMessageConsole;

public class SVBuildConsoleListener 
	implements ISVBuilderOutputListener, Runnable {
	private Map<String, SVConsole>	fProjectBuildConsoleMap = new HashMap<String, SVConsole>();
	private SVConsole					fGlobalBuildConsole = null;
	private List<Message>					fMessageQueue;
	private boolean							fMessageScheduled;
	
	private static class Message {
		public String			fProject;
		public String			fMsg;
		public boolean			fIsErr;
		
		public Message(
				String  project, 
				String  msg,
				boolean is_err) {
			fProject = project;
			fMsg = msg;
			fIsErr = is_err;
		}
	}
	
	public SVBuildConsoleListener() {
		fMessageQueue = new ArrayList<SVBuildConsoleListener.Message>();
	}
	
	private void queue(Message msg) {
		synchronized (fMessageQueue) {
			fMessageQueue.add(msg);
			
			if (!fMessageScheduled) {
				Display.getDefault().asyncExec(this);
				fMessageScheduled = true;
			}
		}
		
	}
	
	public void run() {
		synchronized (fMessageQueue) {
			for (Message m : fMessageQueue) {
//				SVConsole global = getGlobalBuildConsole();
//				SVConsole project = getProjectBuildConsole(m.fProject);
			
//				if (m.fIsErr) {
//					global.getStderr().println(m.fMsg);
//					project.getStderr().println(m.fMsg);
//				} else {
//					global.getStdout().println(m.fMsg);
//					project.getStdout().println(m.fMsg);
//				}
			}
			fMessageQueue.clear();
			fMessageScheduled = false;
		}
	}

	@Override
	public void println(String project, String msg) {
		queue(new Message(project, msg, false));
	}

	@Override
	public void errln(String project, String msg) {
		queue(new Message(project, msg, true));
	}

//	private SVConsole getGlobalBuildConsole() {
//		if (fGlobalBuildConsole == null) {
//			fGlobalBuildConsole = getBuildConsole("SV Global Build Console");
//		}
//		return fGlobalBuildConsole;
//	}
	
//	private SVConsole getProjectBuildConsole(String project) {
//		SVConsole c = fProjectBuildConsoleMap.get(project);
//		
//		if (c == null) {
//			c = getBuildConsole("SV Build Console [" + project + "]");
//			fProjectBuildConsoleMap.put(project, c);
//		}
//		
//		return c;
//  }
//	
//	private SVConsole getBuildConsole(String name) {
//		return SVConsole.getConsole(name, "sve.build");
//	}
}
