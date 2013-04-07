package net.sf.sveditor.ui.wizards.templates;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.StringInputStream;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.ISetSelectionTarget;

public class NewSVTDescriptorWizard extends Wizard implements INewWizard {
	
	private IWorkbench					fWorkbench;
	private IStructuredSelection		fSelection;
	private NewSVTDescriptorPage		fPage;

	public NewSVTDescriptorWizard() {
		// TODO Auto-generated constructor stub
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		fWorkbench = workbench;
		fSelection = selection;
	}
	
	@Override
	public void addPages() {
		IContainer container = null;
		
		if (fSelection != null) {
			if (fSelection.getFirstElement() instanceof IContainer) {
				container = (IContainer)fSelection.getFirstElement();
			} else if (fSelection.getFirstElement() instanceof IResource) {
				container = ((IResource)fSelection.getFirstElement()).getParent();
			}
		}
		fPage = new NewSVTDescriptorPage(container);
		
		addPage(fPage);
	}

	// ECLIPSE: Begin code borrowed from Eclipse platform
    /**
     * Selects and reveals the newly added resource in all parts
     * of the active workbench window's active page.
     *
     * @see ISetSelectionTarget
     */
    protected void selectAndReveal(IResource newResource) {
        selectAndReveal(newResource, fWorkbench.getActiveWorkbenchWindow());
    }

    /**
     * Attempts to select and reveal the specified resource in all
     * parts within the supplied workbench window's active page.
     * <p>
     * Checks all parts in the active page to see if they implement <code>ISetSelectionTarget</code>,
     * either directly or as an adapter. If so, tells the part to select and reveal the
     * specified resource.
     * </p>
     *
     * @param resource the resource to be selected and revealed
     * @param window the workbench window to select and reveal the resource
     * 
     * @see ISetSelectionTarget
     */
    public static void selectAndReveal(IResource resource,
            IWorkbenchWindow window) {
        // validate the input
        if (window == null || resource == null) {
			return;
		}
        IWorkbenchPage page = window.getActivePage();
        if (page == null) {
			return;
		}

        // get all the view and editor parts
        List<IWorkbenchPart> parts = new ArrayList<IWorkbenchPart>();
        IWorkbenchPartReference refs[] = page.getViewReferences();
        for (int i = 0; i < refs.length; i++) {
            IWorkbenchPart part = refs[i].getPart(false);
            if (part != null) {
				parts.add(part);
			}
        }
        refs = page.getEditorReferences();
        for (int i = 0; i < refs.length; i++) {
            if (refs[i].getPart(false) != null) {
				parts.add(refs[i].getPart(false));
			}
        }

        final ISelection selection = new StructuredSelection(resource);
        Iterator<IWorkbenchPart> itr = parts.iterator();
        while (itr.hasNext()) {
            IWorkbenchPart part = itr.next();

            // get the part's ISetSelectionTarget implementation
            ISetSelectionTarget target = null;
            if (part instanceof ISetSelectionTarget) {
				target = (ISetSelectionTarget) part;
			} else {
				target = (ISetSelectionTarget) part
                        .getAdapter(ISetSelectionTarget.class);
			}

            if (target != null) {
                // select and reveal resource
                final ISetSelectionTarget finalTarget = target;
                window.getShell().getDisplay().asyncExec(new Runnable() {
                    public void run() {
                        finalTarget.selectReveal(selection);
                    }
                });
            }
        }
    }
	// ECLIPSE: End code borrowed from Eclipse platform

    // 
	@Override
	public boolean performFinish() {
		IContainer folder = fPage.getFolder();
		String filename = fPage.getFilename() + ".svt";
		
		if (folder == null) {
			return false;
		}
		
		IFile file = folder.getFile(new Path(filename));
		
		try {
			StringInputStream in = new StringInputStream(
					"<sv_template>\n" +
					"</sv_template>\n");
			file.create(in, true, new NullProgressMonitor());
		} catch (CoreException e) {
			return false;
		}

        selectAndReveal(file);

        // Open editor on new file.
        IWorkbenchWindow dw = fWorkbench.getActiveWorkbenchWindow();
        try {
            if (dw != null) {
                IWorkbenchPage page = dw.getActivePage();
                if (page != null) {
                    IDE.openEditor(page, file, true);
                }
            }
        } catch (PartInitException e) {
        	/*
            DialogUtil.openError(dw.getShell(), ResourceMessages.FileResource_errorMessage, 
                    e.getMessage(), e);
			 */
        }

        return true;
	}

}
