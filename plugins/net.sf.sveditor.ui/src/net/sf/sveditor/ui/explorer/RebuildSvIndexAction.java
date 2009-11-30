package net.sf.sveditor.ui.explorer;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
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
		private LogHandle					fLog;
		
		public RebuildIndexAction() {
			super("Rebuild SV Index");
			fLog = LogFactory.getDefault().getLogHandle("RebuildIndexAction");
		}
		
		@SuppressWarnings("unchecked")
		public void run() {
			
			IStructuredSelection sel_s = (IStructuredSelection)
				getActionSite().getViewSite().getSelectionProvider().getSelection();
			updateSelection(sel_s);

			List<IProject> projects = new ArrayList<IProject>();
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();

			fLog.debug("run()");
			
			for (Object sel_o : sel_s.toList()) {
				IProject p = null;
				if (sel_o instanceof IProject) {
					p = (IProject)sel_o;
				} else if (sel_o instanceof IResource) {
					p = ((IResource)sel_o).getProject();
				}
				
				if (p != null && !projects.contains(p)) {
					projects.add(p);
				}
			}
			
			for (IProject p : projects) {
				fLog.debug("Rebuild index for project \"" + p.getName() + "\"");
				rgy.rebuildIndex(p.getName());
			}
		}
	}

}
