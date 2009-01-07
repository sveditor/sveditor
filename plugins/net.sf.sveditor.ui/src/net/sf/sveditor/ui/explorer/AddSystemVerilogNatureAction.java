package net.sf.sveditor.ui.explorer;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.actions.SelectionListenerAction;
import org.eclipse.ui.navigator.CommonActionProvider;
import org.eclipse.ui.navigator.ICommonActionExtensionSite;
import org.eclipse.ui.navigator.ICommonMenuConstants;

public class AddSystemVerilogNatureAction extends CommonActionProvider {

	public AddSystemVerilogNatureAction() {
		
		System.out.println("AddSystemVerilogNatureAction()");
		// TODO Auto-generated constructor stub
	}
	
	@Override
	public void init(ICommonActionExtensionSite site) {
		// TODO Auto-generated method stub
		super.init(site);
		System.out.println("AddSystemVerilogNature.init()");
		
		fAddSVNature = new AddSVNatureAction();
	}



	@Override
	public void fillContextMenu(IMenuManager menu) {
		
//		System.out.println("AddSystemVerilogNature.fillContextMenu()");
		menu.insertAfter(ICommonMenuConstants.GROUP_ADDITIONS, fAddSVNature);
		fAddSVNature.selectionChanged(
				(IStructuredSelection)getContext().getSelection());
	}
	
	
	private AddSVNatureAction				fAddSVNature;
	
	private class AddSVNatureAction extends SelectionListenerAction {

		public AddSVNatureAction() {
			super("Add SV Project Nature");
		}

		@Override
		@SuppressWarnings("unchecked")
		public void run() {
			System.out.println("Action.run()");
			List<IResource> sel = (List<IResource>)getSelectedResources();
			
			for (IResource r : sel) {
				if (r instanceof IProject) {
					IProject p = (IProject)r;
					IProjectNature n = null;
					try {
						p.refreshLocal(IResource.DEPTH_ONE, null);
						n = p.getNature(
								SVCorePlugin.PLUGIN_ID + ".SVProjectNature");
					} catch (CoreException e) { }
					
					if (n == null) {
						try {
							IProjectDescription d = p.getDescription();
							
							String old_ids[] = d.getNatureIds();
							String new_ids[] = new String[old_ids.length+1];
							
							System.out.println("old_ids.length=" + old_ids.length);

							System.arraycopy(old_ids, 0, new_ids, 0, 
									old_ids.length);
						
							new_ids[old_ids.length] = 
								SVCorePlugin.PLUGIN_ID + ".SVNature";
							
							d.setNatureIds(new_ids);
							
							p.setDescription(d, IResource.NONE, null);
						} catch (CoreException e) {
							e.printStackTrace();
						}
					}
				}
				System.out.println("r=" + r.getName());
			}
			super.run();
		}
	}
}
