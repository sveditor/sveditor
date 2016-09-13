/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.wizards;

import java.lang.reflect.InvocationTargetException;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.XMLTransformUtils;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.tagproc.DynamicTemplateParameterProvider;
import net.sf.sveditor.core.tagproc.TagProcessor;
import net.sf.sveditor.core.tagproc.TemplateParameterProvider;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.templates.TemplateTranslator;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

abstract public class AbstractNewSVItemFileWizard extends BasicNewResourceWizard {
//	public static final String				ID = SVUiPlugin.PLUGIN_ID + ".newSVClassWizard";
	protected AbstractNewSVItemFileWizardPage		fPage;
	protected TagProcessor							fTagProc;
	protected TemplateParameterProvider				fTags;
	protected StringBuilder							fTemplate;

	public AbstractNewSVItemFileWizard() {
		super();
		fTemplate = new StringBuilder();
		fTagProc = new TagProcessor();
		fTags = new TemplateParameterProvider();
		fTagProc.addParameterProvider(fTags);
		IPreferenceStore prefs = SVUiPlugin.getDefault().getPreferenceStore();
		Map<String, String>	props = null;
		String params = prefs.getString(SVEditorPrefsConstants.P_SV_TEMPLATE_PROPERTIES);
		
		try {
			props = XMLTransformUtils.xml2Map(params, "parameters", "parameter");
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		if (props != null) {
			fTagProc.addParameterProvider(new TemplateParameterProvider(props));
		}
		
		fTagProc.addParameterProvider(new DynamicTemplateParameterProvider());
	}
	
	abstract protected AbstractNewSVItemFileWizardPage createPage();
	
	abstract protected void generate(IProgressMonitor monitor, IFile file_path);
	
	public void addPages() {
		super.addPages();
		
		fPage = createPage();
		Object sel = getSelection().getFirstElement();
		IResource r = null;
		
		if (sel != null) {
			if (sel instanceof IResource) {
				r = (IResource)sel;
			} else if (sel instanceof IAdaptable) {
				r = (IResource)((IAdaptable)sel).getAdapter(IResource.class);
			}
		}
		
		if (r != null) {
			if (!(r instanceof IContainer)) {
				r = r.getParent();
			}
			fPage.setOption(AbstractNewSVItemFileWizardPage.SOURCE_FOLDER,
					r.getFullPath().toOSString());
		}
		addPage(fPage);
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		super.init(workbench, selection);
		setNeedsProgressMonitor(true);
	}
	
	protected ISVDBIndexIterator getIndexIterator(IProgressMonitor monitor) {
		ISVDBIndexIterator index_it = null;
		if (fPage.getProjectData() != null) {
			index_it = fPage.getProjectData().getProjectIndexMgr();
		}

		return index_it;
	}
	
	protected SVDBIndexCollection getIndexCollection() {
		if (fPage.getProjectData() != null) {
			return fPage.getProjectData().getProjectIndexMgr();
		}
		return null;
	}

	@Override
	public boolean performFinish() {
		IContainer c = SVFileUtils.getWorkspaceFolder(
				fPage.getOption(AbstractNewSVItemFileWizardPage.SOURCE_FOLDER, null));
		final IFile file_path = c.getFile(new Path(
				fPage.getOption(AbstractNewSVItemFileWizardPage.FILE_NAME, null)));
		
		IRunnableWithProgress op = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor) throws InvocationTargetException,
					InterruptedException {
				generate(monitor, file_path);
			}
		};
		
		try {
			getContainer().run(false, false, op);
		} catch (Exception e) {
			return false;
		}
		
		try {
			SVEditorUtil.openEditor("${workspace_loc}/" + file_path.getFullPath());
		} catch (PartInitException e) {
			e.printStackTrace();
		}

		return true;
	}


}
