package net.sf.sveditor.ui.wizards.templates;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

public class ClassBrowseDialog extends Dialog {
	private String						fSelectedClassStr = "";
	private String						fSourceFolder;
	
	// Ignore for now
	private String						fClassParent;
	
	private Text						fFilterText;
	private String						fFilterStr;
	private TableViewer					fTable;
	private List<SVDBDeclCacheItem>		fAllClasses;
	
	
	public ClassBrowseDialog(
			Shell 		parent, 
			String 		src_folder,
			String		class_parent) {
		super(parent);
		fSourceFolder = src_folder;
		fClassParent = class_parent;
		
		fFilterStr = "";
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		Composite c = new Composite(parent, SWT.NONE);
		GridData gd;
		
		SVDBProjectData pdata = getProjectData();
		c.setLayout(new GridLayout());
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		c.setLayoutData(gd);
		
		if (pdata != null) {
			fFilterText = new Text(c, SWT.ICON_CANCEL+SWT.BORDER+SWT.SINGLE);
			gd = new GridData(SWT.FILL, SWT.FILL, true, false);
			fFilterText.setLayoutData(gd);
			fFilterText.addModifyListener(modifyListener);

			fTable = new TableViewer(c);
			gd = new GridData(SWT.FILL, SWT.FILL, true, true);
			gd.heightHint = 200;
			gd.widthHint = 200;
			fTable.getTable().setLayoutData(gd);
			fTable.addSelectionChangedListener(selectionChangedListener);
			fTable.addFilter(viewerFilter);
			fTable.setContentProvider(contentProvider);
			fTable.setLabelProvider(new SVTreeLabelProvider());
			
			SVDBIndexCollection mgr = pdata.getProjectIndexMgr();
			fAllClasses = mgr.findGlobalScopeDecl(new NullProgressMonitor(), "", 
					new ISVDBFindNameMatcher() {
						public boolean match(ISVDBNamedItem it, String name) {
							return (it.getType() == SVDBItemType.ClassDecl);
						}
					});
			
			
			fTable.setInput(fAllClasses);
			
		} else {
			Label l = new Label(c, SWT.NONE);
			l.setText("Error: Unable to find project index data");
		}
		
		return c;
	}
	
	public String getSelectedClass() {
		return fSelectedClassStr;
	}
	
	private IProject findDestProject() {
		IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolder);

		if (c == null) {
			return null;
		} else if (c instanceof IProject) {
			return (IProject)c;
		} else {
			return c.getProject();
		}
	}
	
	public SVDBProjectData getProjectData() {
		IProject p = findDestProject();
		if (p == null) {
			return null;
		}

		SVDBProjectData pdata = 
			SVCorePlugin.getDefault().getProjMgr().getProjectData(p);
		
		return pdata;
	}
	
	private ModifyListener modifyListener = new ModifyListener() {
		public void modifyText(ModifyEvent e) {
			fFilterStr = fFilterText.getText();
			fTable.refresh();
		}
	};

	private ISelectionChangedListener selectionChangedListener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection sel = (IStructuredSelection)event.getSelection();
			SVDBDeclCacheItem item = (SVDBDeclCacheItem)sel.getFirstElement();
			fSelectedClassStr = item.getName();
		}
	};
	
	private ViewerFilter viewerFilter = new ViewerFilter() {
		
		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			SVDBDeclCacheItem item = (SVDBDeclCacheItem)element;
			return item.getName().toLowerCase().startsWith(
					fFilterStr.toLowerCase());
		}
	};
	
	private IStructuredContentProvider contentProvider = new IStructuredContentProvider() {
		
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
		public void dispose() {}
		
		public Object[] getElements(Object inputElement) {
			return fAllClasses.toArray();
		}
	};
}
