package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.ui.actions.SelectionListenerAction;
import org.eclipse.ui.navigator.CommonActionProvider;
import org.eclipse.ui.navigator.ICommonMenuConstants;

public class RebuildSvIndexAction extends CommonActionProvider {

	public RebuildSvIndexAction() {
		fRebuildAction = new RebuildIndexAction();
	}
	
	public void fillContextMenu(IMenuManager menu) {
		menu.insertAfter(ICommonMenuConstants.GROUP_ADDITIONS, fRebuildAction);
	}
	
	private RebuildIndexAction			fRebuildAction;
	
	private class RebuildIndexAction extends SelectionListenerAction {
		public RebuildIndexAction() {
			super("Rebuild SV Index");
		}
		
		@SuppressWarnings("unchecked")
		public void run() {
			List<IProject> projects = new ArrayList<IProject>();
			List<IResource> sel = (List<IResource>)getSelectedResources();
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			
			for (IResource r : sel) {
				IProject p = r.getProject();
				
				if (!projects.contains(p)) {
					projects.add(p);
				}
			}
			
			for (IProject p : projects) {
				rgy.rebuildIndex(p.getName());
			}
		}
	}

}
