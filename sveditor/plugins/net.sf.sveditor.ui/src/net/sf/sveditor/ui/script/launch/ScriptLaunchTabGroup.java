package net.sf.sveditor.ui.script.launch;

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
