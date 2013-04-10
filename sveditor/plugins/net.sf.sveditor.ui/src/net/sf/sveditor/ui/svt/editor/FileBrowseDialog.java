package net.sf.sveditor.ui.svt.editor;

import java.io.File;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class FileBrowseDialog extends Dialog {
	private TreeViewer			fTreeViewer;
	private IContainer			fContainer;
	private File				fContainerFile;
	private String				fSelectedFile;
	
	
	public FileBrowseDialog(Shell shell, IContainer container) {
		super(shell);
		fContainer = container;
		fContainerFile = null;
	}

	public FileBrowseDialog(Shell shell, File container) {
		super(shell);
		fContainer = null;
		fContainerFile = container;
	}

	public String getSelectedFile() {
		return fSelectedFile;
	}
	
	@Override
	protected Control createDialogArea(Composite p) {
		Composite parent = new Composite(p, SWT.NONE);
		parent.setLayout(new GridLayout(1, true));
		
		fTreeViewer = new TreeViewer(parent);
		
		GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.widthHint = 300;
		gd.heightHint = 300;
		fTreeViewer.getControl().setLayoutData(gd);
		fTreeViewer.setAutoExpandLevel(2);
		
		if (fContainer != null) {
			fTreeViewer.setContentProvider(new WorkbenchContentProvider());
			fTreeViewer.addFilter(new ViewerFilter() {

				@Override
				public boolean select(Viewer viewer, Object parentElement,
						Object element) {
					boolean ret = true;

					// TODO: ensure this element is a child of Container
					
					return ret;
				}
			});

			fTreeViewer.setLabelProvider(WSLabelProvider);
			fTreeViewer.setInput(ResourcesPlugin.getWorkspace());
			fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
				public void selectionChanged(SelectionChangedEvent event) {
					IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
					if (sel.getFirstElement() != null) {
						IResource r = (IResource)sel.getFirstElement();
						StringBuilder sb = new StringBuilder();
						
						while (r != null && !fContainer.equals(r)) {
							if (sb.length() > 0) {
								sb.insert(0, r.getName() + "/");
							} else {
								sb.insert(0, r.getName());
							}
							r = r.getParent();
						}
						fSelectedFile = sb.toString();
					}
				}
			});
		} else {
			fTreeViewer.setContentProvider(FSContentProvider);
			fTreeViewer.setLabelProvider(FSLabelProvider);
			fTreeViewer.setInput(new Object());
			fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {
				public void selectionChanged(SelectionChangedEvent event) {
					IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
					if (sel.getFirstElement() != null) {
						File r = (File)sel.getFirstElement();
						StringBuilder sb = new StringBuilder();
						
						while (r != null && !fContainerFile.equals(r)) {
							if (sb.length() > 0) {
								sb.insert(0, r.getName() + "/");
							} else {
								sb.insert(0, r.getName());
							}
							r = r.getParentFile();
						}
						fSelectedFile = sb.toString();
					}
				}
			});
		}
		
		
		if (fContainer != null) {
			fTreeViewer.setSelection(new StructuredSelection(fContainer), true);
		}
		

		return fTreeViewer.getControl();
	}
	
	private ITreeContentProvider FSContentProvider = new ITreeContentProvider() {
		
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
		public void dispose() {}
		
		public boolean hasChildren(Object element) {
			File f = (File)element;
			
			return (f.listFiles() != null && f.listFiles().length > 0);
		}
		
		public Object getParent(Object element) {
			return ((File)element).getParentFile();
		}
		
		public Object[] getElements(Object inputElement) {
			return new Object[] {fContainerFile};  
		}
		
		public Object[] getChildren(Object parentElement) {
			File files[] = ((File)parentElement).listFiles();
			
			if (files == null) {
				return new Object[0];
			} else {
				return files;
			}
		}
	};
	
	private WorkbenchLabelProvider WSLabelProvider = new WorkbenchLabelProvider();

	private static final Image IMG_FOLDER = PlatformUI.getWorkbench()
			.getSharedImages().getImage(ISharedImages.IMG_OBJ_FOLDER);

	private static final Image IMG_FILE = PlatformUI.getWorkbench()
			.getSharedImages().getImage(ISharedImages.IMG_OBJ_FILE);			

	private LabelProvider FSLabelProvider = new LabelProvider() {

		@Override
		public Image getImage(Object element) {
			File f = (File)element;
			if (f.isDirectory()) {
				return IMG_FOLDER;
			} else {
				return IMG_FILE;
			}
		}

		@Override
		public String getText(Object element) {
			File f = (File)element;
			return f.getName();
		}
		
	};
}
