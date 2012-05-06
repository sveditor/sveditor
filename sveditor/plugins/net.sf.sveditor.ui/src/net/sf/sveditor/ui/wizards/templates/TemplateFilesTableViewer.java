package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.text.TagProcessor;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TableColumn;

public class TemplateFilesTableViewer extends TableViewer {
	private TemplateInfo					fTemplate;
	private String							fSourceFolderStr = "";
	private List<String>					fFilenames;
	private TagProcessor					fTagProcessor;
	
	public TemplateFilesTableViewer(Composite parent, TagProcessor p) {
		super(parent);
		getTable().setHeaderVisible(true);
		
		TableColumn err = new TableColumn(getTable(), SWT.LEFT, 0);
		err.setText("Status");
		err.setWidth(50);
		
		TableColumn file = new TableColumn(getTable(), SWT.LEFT, 1);
		file.setText("Filename");
		file.setWidth(400);
		
		setContentProvider(contentProvider);
		setLabelProvider(labelProvider);
		
		fTagProcessor = p;
		
		updateFilenames();
	}
	
	public String validate() {
		String ret = null;
		
		updateFilenames();
		
		IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolderStr);
		if (c != null) {
			// TODO: validate all proposed files to ensure none exist
			fTemplate.getTemplates();
			for (String filename : fFilenames) {
				IFile file = c.getFile(new Path(filename));
				if (file.exists() && ret == null) {
					ret = "File \"" + filename + "\" exists";
				}
			}
		} else {
			ret = "Directory \"" + fSourceFolderStr + "\" does not exist";
		}

		return ret;
	}
	
	public void setSourceFolder(String src_folder) {
		fSourceFolderStr = src_folder;
		updateFilenames();
	}
	
	public void setTemplate(TemplateInfo template) {
		fTemplate = template;
		updateFilenames();
	}
	
	private void updateFilenames() {
		fFilenames = new ArrayList<String>();
		
		if (fTemplate != null) {
			for (Tuple<String, String> n : fTemplate.getTemplates()) {
				fFilenames.add("" + fSourceFolderStr + "/" + n.second());
			}
		}
		
		// TODO: process filenames
		for (int i=0; i<fFilenames.size(); i++) {
			String pn = fTagProcessor.process(fFilenames.get(i));
			fFilenames.set(i, pn);
		}
		
		if (getTable() != null && !getTable().isDisposed()) {
			setInput(fFilenames);
		}
	}
	
	private IStructuredContentProvider contentProvider = new IStructuredContentProvider() {
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
		public void dispose() {}

		@SuppressWarnings("rawtypes")
		public Object[] getElements(Object inputElement) {
			return ((List)inputElement).toArray();
		}
	};
	
	private ITableLabelProvider labelProvider = new ITableLabelProvider() {
		public void removeListener(ILabelProviderListener listener) {}
		public void addListener(ILabelProviderListener listener) {}
		public void dispose() {}
		
		public boolean isLabelProperty(Object element, String property) {
			return false;
		}
		
		public String getColumnText(Object element, int columnIndex) {
			if (columnIndex == 1) {
				// Filename column
				return element.toString();
			} else {
				return null;
			}
		}
		
		public Image getColumnImage(Object element, int columnIndex) {
			if (columnIndex == 0) {
				IContainer c = SVFileUtils.getWorkspaceFolder(fSourceFolderStr);
				
				if (c != null) {
					String filename = element.toString();
					IFile file = c.getFile(new Path(filename));

					if (file.exists()) {
						return SVUiPlugin.getImage("/icons/eview16/error.gif");
					} else {
						return SVUiPlugin.getImage("/icons/eview16/signed_yes.gif");
					}
				} else {
					return SVUiPlugin.getImage("/icons/eview16/error.gif");
				}
			} else {
				return null;
			}
		}
	};

}
