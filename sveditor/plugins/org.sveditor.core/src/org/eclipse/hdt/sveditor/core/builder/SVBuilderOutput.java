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
package org.sveditor.core.builder;

public class SVBuilderOutput implements ISVBuilderOutput {
	private String						fProject;
	private ISVBuilderOutputListener	fListener;
	
	public SVBuilderOutput(
			String						project,
			ISVBuilderOutputListener 	l
			) {
		fProject = project;
		fListener = l;
	}

	@Override
	public void println(String msg) {
		fListener.println(fProject, msg);
	}

	@Override
	public void note(String msg) {
		println("[Note] " + msg);
	}

	@Override
	public void errln(String msg) {
		fListener.errln(fProject, msg);
	}

	@Override
	public void error(String msg) {
		errln("[Error] " + msg);
	}

}
