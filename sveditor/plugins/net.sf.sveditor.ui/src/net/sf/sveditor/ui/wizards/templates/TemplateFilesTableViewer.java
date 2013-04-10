package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.templates.TemplateParameterProvider;
import net.sf.sveditor.core.text.TagProcessor;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
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
	private TemplateParameterProvider		fParameters;
	private boolean						fOverwriteFiles;
	
	public TemplateFilesTableViewer(Composite parent, TemplateParameterProvider p) {
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
		
		fParameters = p;
		
		updateFilenames();
	}
	
	public void setOverwriteFiles(boolean overwrite) {
		fOverwriteFiles = overwrite;
		updateFilenames();
	}
	
	public String validate() {
		String ret = null;
		
		updateFilenames();
		
		if (!fParameters.hasTag("name") || 
				fParameters.getTag("name").trim().equals("")) {
			ret = "Must specify name";
		}

		String s = fSourceFolderStr;
		
		if (s == null) {
			s = "";
		}
		
		IContainer c = SVFileUtils.getWorkspaceFolder(s);
		if (c != null && c.exists()) {
			// TODO: validate all proposed files to ensure none exist
			fTemplate.getTemplates();
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			for (String filename : fFilenames) {
				IFile file = root.getFile(new Path(filename));
				if ((file.exists() && !fOverwriteFiles) && ret == null) {
					ret = "File \"" + filename + "\" exists";
				}
			}
		} else {
			ret = "Directory \"" + s + "\" does not exist";
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
		
		TemplateParameterProvider pp = new TemplateParameterProvider(fParameters);
		TagProcessor tp = new TagProcessor();
		tp.addParameterProvider(pp);
		
		if (pp.hasTag("name") && pp.getTag("name").trim().equals("")) {
			pp.removeTag("name");
		}
		
		if (fTemplate != null) {
			for (Tuple<String, String> n : fTemplate.getTemplates()) {
				fFilenames.add("" + fSourceFolderStr + "/" + n.second());
			}
		}
		
		// process filenames
		for (int i=0; i<fFilenames.size(); i++) {
			String pn = tp.process(fFilenames.get(i));
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
				IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

				if (c != null) {
					String filename = element.toString();
					IFile file = root.getFile(new Path(filename));

					if (!fParameters.hasTag("name") || 
							fParameters.getTag("name").trim().equals("") || 
							(file.exists() && !fOverwriteFiles)) {
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
