package net.sf.sveditor.ui.batch;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTabGroup;
import org.eclipse.debug.ui.CommonTab;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.debug.ui.ILaunchConfigurationTab;

public class JavaScriptLauncherTabGroup extends
		AbstractLaunchConfigurationTabGroup {

	public JavaScriptLauncherTabGroup() {
		// TODO Auto-generated constructor stub
	}

	public void createTabs(ILaunchConfigurationDialog dialog, String mode) {
		List<ILaunchConfigurationTab> tabs = new ArrayList<ILaunchConfigurationTab>();
	
		tabs.add(new JavaScriptLauncherScriptTab());
		tabs.add(new CommonTab());
		
		setTabs(tabs.toArray(new ILaunchConfigurationTab[tabs.size()]));
	}

	
}
