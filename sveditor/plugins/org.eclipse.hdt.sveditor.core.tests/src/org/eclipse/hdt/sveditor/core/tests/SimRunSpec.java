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
package net.sf.sveditor.core.tests;

import java.util.ArrayList;
import java.util.List;

public class SimRunSpec {
	private List<String>			fTopModules;
	private List<String>			fSimOpts;
	private String					fTranscriptPath;
	
	public SimRunSpec() {
		fTopModules = new ArrayList<String>();
		fSimOpts = new ArrayList<String>();
	}
	
	public void addTopModule(String top) {
		fTopModules.add(top);
	}
	
	public List<String> getTopModules() {
		return fTopModules;
	}
	
	public void addSimOptions(String opt) {
		fSimOpts.add(opt);
	}
	
	public List<String> getSimOptions() {
		return fSimOpts;
	}
	
	public String getTranscriptPath() {
		return fTranscriptPath;
	}

	public void setTranscriptPath(String path) {
		fTranscriptPath = path;
	}

}
