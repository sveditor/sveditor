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
package org.sveditor.ui.script.launch;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTabGroup;
import org.eclipse.debug.ui.CommonTab;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.debug.ui.ILaunchConfigurationTab;

public class ScriptLaunchTabGroup extends
		AbstractLaunchConfigurationTabGroup {

	public ScriptLaunchTabGroup() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public void createTabs(ILaunchConfigurationDialog dialog, String mode) {
		List<ILaunchConfigurationTab> tabs = new ArrayList<ILaunchConfigurationTab>();
		
		tabs.add(new ScriptLauncherScriptTab());
		tabs.add(new CommonTab());
		
		setTabs(tabs.toArray(new ILaunchConfigurationTab[tabs.size()]));		
	}

}
