package net.sf.sveditor.ui.prop_pages;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

public class PluginLibPrefsPage implements ISVProjectPropsPage,
	IStructuredContentProvider, ILabelProvider {
	private CheckboxTableViewer					fPluginLibViewer;
	private List<SVDBPluginLibDescriptor>		fPluginLibs;
	private SVProjectFileWrapper				fProjectWrapper;
	
	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
	}

	public PluginLibPrefsPage() {
		fPluginLibs = SVCorePlugin.getDefault().getPluginLibList();
	}

	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(1, true));
		
		fPluginLibViewer = CheckboxTableViewer.newCheckList(
				frame, SWT.NONE);
		fPluginLibViewer.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fPluginLibViewer.setContentProvider(this);
		fPluginLibViewer.setLabelProvider(this);
		fPluginLibViewer.setInput(fPluginLibs);
		
		for (SVDBPluginLibDescriptor lib : fPluginLibs) {
			int sel = -1;
			for (int i=0; i<fProjectWrapper.getPluginPaths().size(); i++) {
				SVDBPath p = fProjectWrapper.getPluginPaths().get(i);

				if (p.getPath().equals(lib.getId())) {
					sel = i;
					break;
				}
			}
			
			System.out.println("lib=" + lib.getId() + " sel=" + sel);
			if (!fPluginLibViewer.setChecked(lib, (sel != -1))) {
				System.out.println("Failed to set checked state");
			}
		}
		return frame;
	}

	public Image getIcon() {
		return SVUiPlugin.getImage("/icons/eview16/plugin_lib.gif");
	}

	public String getName() {
		return "Pre-Packaged Libs";
	}


	public void perfomOk() {
		
		fProjectWrapper.getPluginPaths().clear();
		
		for (int i=0; i<fPluginLibs.size(); i++) {
			if (fPluginLibViewer.getChecked(fPluginLibs.get(i))) {
				System.out.println("saving lib " + fPluginLibs.get(i).getId());
				SVDBPath p = new SVDBPath(fPluginLibs.get(i).getId(), false);
				fProjectWrapper.getPluginPaths().add(p);
			}
		}
	}

	public Object[] getElements(Object inputElement) {
		return fPluginLibs.toArray();
	}

	public void dispose() {
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	public Image getImage(Object element) {
		return null;
	}

	public String getText(Object element) {
		if (element instanceof SVDBPluginLibDescriptor) {
			return ((SVDBPluginLibDescriptor)element).getName();
		}
		return null;
	}

	public void addListener(ILabelProviderListener listener) {}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {}
	
	

}
