/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import java.io.File;
import java.net.URI;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBFileOverrideIndexIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.SVDBShadowIndexFactory;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.project.ISVDBProjectSettingsListener;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.actions.AddBlockCommentAction;
import net.sf.sveditor.ui.editor.actions.FindReferencesAction;
import net.sf.sveditor.ui.editor.actions.IndentAction;
import net.sf.sveditor.ui.editor.actions.NextWordAction;
import net.sf.sveditor.ui.editor.actions.OpenDeclarationAction;
import net.sf.sveditor.ui.editor.actions.OpenDiagForSelectionAction;
import net.sf.sveditor.ui.editor.actions.OpenObjectsViewAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickHierarchyAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickObjectsViewAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickOutlineAction;
import net.sf.sveditor.ui.editor.actions.OpenTypeHierarchyAction;
import net.sf.sveditor.ui.editor.actions.OverrideTaskFuncAction;
import net.sf.sveditor.ui.editor.actions.PrevWordAction;
import net.sf.sveditor.ui.editor.actions.RemoveBlockCommentAction;
import net.sf.sveditor.ui.editor.actions.SelNextWordAction;
import net.sf.sveditor.ui.editor.actions.SelPrevWordAction;
import net.sf.sveditor.ui.editor.actions.ToggleCommentAction;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.information.IInformationPresenter;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.MatchingCharacterPainter;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.ITextEditorHelpContextIds;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IDEActionFactory;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AddTaskAction;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class SVEditor extends TextEditor 
	implements ISVDBProjectSettingsListener, ISVEditor, ILogLevel {

	private SVOutlinePage					fOutline;
	private SVHighlightingManager			fHighlightManager;
	private SVCodeScanner					fCodeScanner;
	private MatchingCharacterPainter		fMatchingCharacterPainter;
	private SVCharacterPairMatcher			fCharacterMatcher;
	private SVDBFile						fSVDBFile;
	private ISVDBIndex						fSVDBIndex;
	private String							fFile;
	private SVDBIndexCollection				fIndexMgr;
	private LogHandle						fLog;
	private String							fSVDBFilePath;
	private UpdateProjectSettingsJob		fProjectSettingsJob;
	private SVDBProjectData					fPendingProjectSettingsUpdate;
	private UpdateSVDBFileJob				fUpdateSVDBFileJob;
	private boolean						fPendingUpdateSVDBFile;
	private SVDBFileOverrideIndexIterator	fIndexIterator;
	
	
	IInformationPresenter fQuickObjectsPresenter;
	IInformationPresenter fQuickOutlinePresenter;
	IInformationPresenter fQuickHierarchyPresenter;
	
	public IInformationPresenter getQuickObjectsPresenter() {
		if(fQuickObjectsPresenter == null) {
			fQuickObjectsPresenter = 
					((SVSourceViewerConfiguration)getSourceViewerConfiguration())
					.getObjectsPresenter(getSourceViewer(), false) ;
			if(fQuickObjectsPresenter != null) {
				fQuickObjectsPresenter.install(getSourceViewer()) ;
			}
		}
		return fQuickObjectsPresenter ;
	}
	
	public IInformationPresenter getQuickOutlinePresenter() {
		if(fQuickOutlinePresenter == null) {
			fQuickOutlinePresenter = 
					((SVSourceViewerConfiguration)getSourceViewerConfiguration())
					.getOutlinePresenter(getSourceViewer(), false) ;
			if(fQuickOutlinePresenter != null) {
				fQuickOutlinePresenter.install(getSourceViewer()) ;
			}
		}
		return fQuickOutlinePresenter ;
	}
	
	public IInformationPresenter getQuickHierarchyPresenter() {
		if(fQuickHierarchyPresenter == null) {
			fQuickHierarchyPresenter = 
					((SVSourceViewerConfiguration)getSourceViewerConfiguration())
					.getHierarchyPresenter(getSourceViewer(), false) ;
			if(fQuickHierarchyPresenter != null) {
				fQuickHierarchyPresenter.install(getSourceViewer()) ;
			}
		}
		return fQuickHierarchyPresenter ;
	}
	
	
	private class UpdateSVDBFileJob extends Job {
		public UpdateSVDBFileJob() {
			super("Update SVDBFile");
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			IEditorInput ed_in = getEditorInput();
			IDocument doc = getDocumentProvider().getDocument(ed_in);
			StringInputStream sin = new StringInputStream(doc.get());
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

			SVDBFile new_in = fIndexMgr.parse(
					getProgressMonitor(), sin, fSVDBFilePath, markers);
			fSVDBFile.clearChildren();
			
			if (new_in != null) {
				fSVDBFile = new_in;

				addErrorMarkers(markers);
			}

			if (fOutline != null) {
				fOutline.refresh();
			}
			
			synchronized (SVEditor.this) {
				fUpdateSVDBFileJob = null;
				if (fPendingUpdateSVDBFile) {
					updateSVDBFile();
				}
			}
			
			return Status.OK_STATUS;
		}
	}
	
	public SVEditor() {
		super();
		
		setDocumentProvider(SVEditorDocumentProvider.getDefault());
		
		fCodeScanner = new SVCodeScanner();
		fCharacterMatcher = new SVCharacterPairMatcher();
		SVUiPlugin.getDefault().getPreferenceStore().addPropertyChangeListener(
				fPropertyChangeListener);
		
		fLog = LogFactory.getLogHandle("SVEditor");
		
		// Check in with the plug-in
		SVUiPlugin.getDefault().startRefreshJob();
	}
	
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		super.init(site, input);
		
		if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			if (uri.getScheme().equals("plugin")) {
				fFile = "plugin:" + uri.getPath();
			} else {
				fFile = uri.getPath();
			}
		} else if (input instanceof IFileEditorInput) {
			fFile = ((IFileEditorInput)input).getFile().getFullPath().toOSString();
		}
		
		fSVDBFile = new SVDBFile(fFile);
		fIndexIterator = new SVDBFileOverrideIndexIterator(fSVDBFile);
		
		// Fixup documents that have \r and not \r\n
		IDocument doc = getDocument();
		int idx=0;
		int replacements=0;
		try {
			while (idx < doc.getLength()) {
				int ch = doc.getChar(idx);
				if (ch == '\r') {
					if (idx+1 < doc.getLength() && doc.getChar(idx+1) != '\n') {
						doc.replace(idx, 1, "\r\n");
						replacements++;
					} else if (idx+1 >= doc.getLength()) {
						// Insert a final '\n'
						doc.replace(idx, 1, "\r\n");
						replacements++;
					}
				}
				idx++;
			}
		} catch (BadLocationException e) {}
		if (replacements > 0) {
			fLog.note("Replaced " + replacements + " occurrences of '\\r' without '\\n' in file " + fFile);
		}
		
		// Hook into the SVDB management structure
		initSVDBMgr();
	}
	
	@Override
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
		
		// TODO: When the user saves the file, clear any cached information
		// on validity.
		
	}

	@Override
	public void doSaveAs() {
		super.doSaveAs();
		
		// TODO: Probably need to make some updates when the name changes
	}

	/**
	 * Called when project settings change. Update our notion of
	 * which index is managing this file
	 */
	public void projectSettingsChanged(SVDBProjectData data) {
		fLog.debug(LEVEL_MID, "projectSettingsChanged: " + fSVDBFilePath);
		synchronized (this) {
			if (fProjectSettingsJob == null) {
				fProjectSettingsJob = new UpdateProjectSettingsJob(this, data.getName());
				fProjectSettingsJob.schedule();
				fPendingProjectSettingsUpdate = null;
			} else {
				fPendingProjectSettingsUpdate = data;
			}
		}
	}

	public void int_projectSettingsUpdated(final ISVDBIndex index, final SVDBIndexCollection index_mgr) {
		fLog.debug(LEVEL_MIN, "projectSettingsUpdated " + fSVDBFilePath + " - index=" + 
				((index != null)?(index.getTypeID() + "::" + index.getBaseLocation()):"null") + 
				" ; index_mgr=" + 
				((index_mgr != null)?(index_mgr.getProject()):"null"));
		
		final SVActionContributor ac = (SVActionContributor)getEditorSite().getActionBarContributor();
		getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
			
			public void run() {
				String msg = "";
				if (index != null) {
					if (index.getTypeID().equals(SVDBShadowIndexFactory.TYPE)) {
						msg = "Index: None";
					} else {
						msg = "Index: " + index.getBaseLocation();
					}
				} else {
					msg = "Index: Problem locating";
				}
				ac.getActionBars().getStatusLineManager().setMessage(msg);
			}
		});
		
		synchronized (this) {
			fProjectSettingsJob = null;
			fSVDBIndex = index;
			fIndexMgr = index_mgr;
			fIndexIterator.setIndexIt(fIndexMgr);
			fIndexIterator.setIndex(fSVDBIndex);
		}
		if (fPendingProjectSettingsUpdate != null) {
			projectSettingsChanged(fPendingProjectSettingsUpdate);
		} else {
			updateSVDBFile();
		}
	}

	private void initSVDBMgr() {
		IEditorInput ed_in = getEditorInput();
		
		SVActionContributor ac = (SVActionContributor)getEditorSite().getActionBarContributor();
		ac.getActionBars().getStatusLineManager().setMessage("Finding association");
		
		if (ed_in instanceof IURIEditorInput) {
			IURIEditorInput uri_in = (IURIEditorInput)ed_in;
			SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();

			if (uri_in.getURI().getScheme().equals("plugin")) {
				fLog.debug(LEVEL_MIN, "Editor path is in a plugin: " + uri_in.getURI());
				fSVDBFilePath = "plugin:" + uri_in.getURI().getPath();
				fSVDBFilePath = SVFileUtils.normalize(fSVDBFilePath);
				
				SVDBPluginLibDescriptor target = null;
				
				String uri_path = uri_in.getURI().getPath();
				String plugin = uri_path.substring(1, uri_path.indexOf('/', 1));
				String root_file = uri_path.substring(uri_path.indexOf('/', 1));
				
				for (SVDBPluginLibDescriptor d : SVCorePlugin.getDefault().getPluginLibList()) {
					if (d.getNamespace().equals(plugin)) {
						String root_dir = new File(d.getPath()).getParent();
						if (!root_dir.startsWith("/")) {
							root_dir = "/" + root_dir;
						}
						
						if (root_file.startsWith(root_dir)) {
							target = d;
							break;
						}
					}
				}
				
				fIndexMgr = new SVDBIndexCollection(rgy.getIndexCollectionMgr(), plugin);

				if (target != null) {
					fLog.debug(LEVEL_MIN, "Found a target plugin library");
					fIndexMgr.addPluginLibrary(rgy.findCreateIndex(
							new NullProgressMonitor(), 
							SVDBIndexRegistry.GLOBAL_PROJECT, target.getId(), 
							SVDBPluginLibIndexFactory.TYPE, null));
				} else {
					fLog.debug(LEVEL_MIN, "Did not find the target plugin library");
				}
			} else { // regular workspace or filesystem path
				if (ed_in instanceof FileEditorInput) {
					FileEditorInput fi = (FileEditorInput)ed_in;
					fLog.debug(LEVEL_MIN, "Path \"" + fi.getFile().getFullPath() + 
							"\" is in project " + fi.getFile().getProject().getName());
					
					// re-adjust
					
					fSVDBFilePath = "${workspace_loc}" + fi.getFile().getFullPath().toOSString();
					fSVDBFilePath = SVFileUtils.normalize(fSVDBFilePath);
					
					fLog.debug(LEVEL_MIN, "Set SVDBFilePath=" + fSVDBFilePath);
					
					projectSettingsChanged(mgr.getProjectData(fi.getFile().getProject()));
					
					mgr.addProjectSettingsListener(this);
				} else {
					// Check whether another
					fLog.debug(LEVEL_MIN, "URI instance: " + uri_in.getClass().getName());
					fSVDBFilePath = SVFileUtils.normalize(uri_in.getURI().getPath());
					fLog.debug(LEVEL_MIN, "Normalizing file \"" + uri_in.getURI().getPath() + "\" to \"" + fSVDBFilePath + "\"");
					fLog.debug(LEVEL_MIN, "File \"" + fSVDBFilePath + "\" is outside the workspace");
					
					fIndexMgr = null;
					Tuple<ISVDBIndex, SVDBIndexCollection> result = 
							SVDBIndexUtil.findIndexFile(fSVDBFilePath, null, true);
					
					// TODO: What happens with no index
					fSVDBIndex = result.first();
					fIndexMgr  = result.second();
					fIndexIterator.setIndex(fSVDBIndex);
					fIndexIterator.setIndexIt(fIndexMgr);
					fLog.debug(LEVEL_MIN, "File will be managed by index \"" + fSVDBIndex.getBaseLocation() + "\"");
				}
			}
		} else {
			fLog.error("SVEditor input is of type " + ed_in.getClass().getName());
		}
	}

	void updateSVDBFile() {
		fLog.debug(LEVEL_MAX, "updateSVDBFile - fIndexMgr=" + fIndexMgr);
		
		if (fIndexMgr != null) {
			if (fUpdateSVDBFileJob == null) {
				synchronized (this) {
					fPendingUpdateSVDBFile = false;
					fUpdateSVDBFileJob = new UpdateSVDBFileJob();
					fUpdateSVDBFileJob.schedule();
				}
			} else {
				fPendingUpdateSVDBFile = true;
			}
		}
	}
	
	public SVCodeScanner getCodeScanner() {
		return fCodeScanner;
	}

	@Override
	protected void initializeKeyBindingScopes() {
		setKeyBindingScopes(new String[] {SVUiPlugin.PLUGIN_ID + ".svEditorContext"});
	}

	@SuppressWarnings("deprecation")
	@Override
	protected void createActions() {
		// TODO Auto-generated method stub
		super.createActions();

		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();
		
		IAction a = new TextOperationAction(bundle,
				"ContentAssistProposal.", this,
				ISourceViewer.CONTENTASSIST_PROPOSALS);

		// Added this call for 2.1 changes
		// New to 2.1 - CTRL+Space key doesn't work without making this call
		a.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS);
		setAction("ContentAssistProposal", a);

		a = new TextOperationAction(bundle, "ContentAssistTip.",
				this, ISourceViewer.CONTENTASSIST_CONTEXT_INFORMATION);

		//	Added this call for 2.1 changes
		a.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_CONTEXT_INFORMATION);
		setAction("ContentAssistTip", a);

		/*
		a = new TextOperationAction(bundle,
				"ContentFormat.", this, ISourceViewer.FORMAT);
		a.setActionDefinitionId("net.sveditor.ui.indent");
		setAction("ContentFormat", a);
		markAsStateDependentAction("Format", true);
		markAsSelectionDependentAction("Format", true);
		 */

		
		// Add the task action to the Edit pulldown menu (bookmark action is
		// 'free')
		ResourceAction ra = new AddTaskAction(bundle, "AddTask.",
				this);
		ra.setHelpContextId(ITextEditorHelpContextIds.ADD_TASK_ACTION);
		ra.setActionDefinitionId(ITextEditorActionDefinitionIds.ADD_TASK);
		setAction(IDEActionFactory.ADD_TASK.getId(), ra);

		//Add action to define the marked area as a folding area
		/*
		a = new DefineFoldingRegionAction(bundle,
				"DefineFoldingRegion.", this); //$NON-NLS-1$
		setAction("DefineFoldingRegion", a);
		 */
		
		OpenDeclarationAction od_action = new OpenDeclarationAction(bundle, this);
		od_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.declaration");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", od_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction", false);
		
		FindReferencesAction fr_action = new FindReferencesAction(bundle, this);
		fr_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.find.references");
		setAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", fr_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", false);

		OpenTypeHierarchyAction th_action = new OpenTypeHierarchyAction(bundle, this);
		th_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.type.hierarchy");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenTypeHierarchyAction", th_action);

		OpenObjectsViewAction ov_action = new OpenObjectsViewAction(bundle);
		ov_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.objects");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenObjectsAction", ov_action);

		OpenQuickObjectsViewAction qov_action = new OpenQuickObjectsViewAction(bundle, this);
		qov_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.quick.objects");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenQuickObjectsAction", qov_action);

		OpenQuickOutlineAction qoutv_action = new OpenQuickOutlineAction(bundle, this);
		qoutv_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.quick.outline");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenQuickOutlineAction", qoutv_action);

		OpenQuickHierarchyAction qh_action = new OpenQuickHierarchyAction(bundle, this);
		qh_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.quick.hierarchy");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenQuickHierarchyAction", qh_action);

		OpenDiagForSelectionAction ods_action = new OpenDiagForSelectionAction(bundle, this);
		ods_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.diag.selection");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenDiagForSelectionAction", ods_action);

		IndentAction ind_action = new IndentAction(bundle, "Indent.", this);
		ind_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".indent");
		setAction(SVUiPlugin.PLUGIN_ID + ".svIndentEditorAction", ind_action);
		
		AddBlockCommentAction add_block_comment = new AddBlockCommentAction(
				bundle, "AddBlockComment.", this);
		add_block_comment.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".AddBlockComment");
		add_block_comment.setEnabled(true);
		setAction(SVUiPlugin.PLUGIN_ID + ".svAddBlockCommentAction", add_block_comment);
		
		RemoveBlockCommentAction remove_block_comment = new RemoveBlockCommentAction(
				bundle, "RemoveBlockComment.", this);
		remove_block_comment.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".RemoveBlockComment");
		remove_block_comment.setEnabled(true);
		setAction(SVUiPlugin.PLUGIN_ID + ".svRemoveBlockCommentAction", remove_block_comment);
		
		ToggleCommentAction toggle_comment = new ToggleCommentAction(bundle, "ToggleComment.", this);
		toggle_comment.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".ToggleComment");
		// TODO: Toggle requires more investigation on how to implement
		toggle_comment.setEnabled(true);
		toggle_comment.configure(getSourceViewer(), getSourceViewerConfiguration());
		setAction(SVUiPlugin.PLUGIN_ID + ".svToggleCommentAction", toggle_comment);
		
		OverrideTaskFuncAction ov_tf_action = new OverrideTaskFuncAction(
				bundle, "OverrideTaskFunc.", this);
		ov_tf_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".override.tf.command");
		setAction(SVUiPlugin.PLUGIN_ID + ".override.tf", ov_tf_action);
		
		NextWordAction nw_action = new NextWordAction(
				bundle, "NextWordAction.", this);
		nw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.WORD_NEXT);
		setAction(ITextEditorActionDefinitionIds.WORD_NEXT, nw_action);
		
		PrevWordAction pw_action = new PrevWordAction(
				bundle, "PrevWordAction.", this);
		pw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.WORD_PREVIOUS);
		setAction(ITextEditorActionDefinitionIds.WORD_PREVIOUS, pw_action);
		
		SelNextWordAction sel_nw_action = new SelNextWordAction(
				bundle, "SelNextWordAction.", this);
		sel_nw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.SELECT_WORD_NEXT);
		setAction(ITextEditorActionDefinitionIds.SELECT_WORD_NEXT, sel_nw_action);
		
		SelPrevWordAction sel_pw_action = new SelPrevWordAction(
				bundle, "SelPrevWordAction.", this);
		sel_pw_action.setActionDefinitionId(ITextEditorActionDefinitionIds.SELECT_WORD_PREVIOUS);
		setAction(ITextEditorActionDefinitionIds.SELECT_WORD_PREVIOUS, sel_pw_action);
		
	}
	
	/*
	private ISVDBItemIterator SVEmptyItemIterator = new ISVDBItemIterator() {
		public ISVDBItemBase nextItem(SVDBItemType... type_list) { return null; }
		public boolean hasNext(SVDBItemType... type_list) { return false; }
	};
	
	private ISVDBIndexIterator SVEditorIndexIterator = new ISVDBIndexIterator() {
		public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
			if (fIndexMgr != null) {
				SVDBIndexCollectionItemIterator it = 
					(SVDBIndexCollectionItemIterator)fIndexMgr.getItemIterator(monitor);

				it.setOverride(fSVDBIndex, fSVDBFile);

				return it;
			} else {
				return SVEmptyItemIterator;
			}
		}

		public List<SVDBDeclCacheItem> findGlobalScopeDecl(
				IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
			return fIndexMgr.findGlobalScopeDecl(monitor, name, matcher);
		}

		public List<SVDBDeclCacheItem> findPackageDecl(
				IProgressMonitor monitor, SVDBDeclCacheItem pkg_item) {
			return fIndexMgr.findPackageDecl(monitor, pkg_item);
		}

		public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
			return fIndexMgr.getDeclFile(monitor, item);
		}
	};
	 */
	
	public ISVDBIndexIterator getIndexIterator() {
		return fIndexIterator;
	}
	
	public IDocument getDocument() {
		return getDocumentProvider().getDocument(getEditorInput());
	}
	
	public ITextSelection getTextSel() {
		ITextSelection sel = null;
		
		ISelection sel_o = getSelectionProvider().getSelection();
		if (sel_o != null && sel_o instanceof ITextSelection) {
			sel = (ITextSelection)sel_o;
		}
		
		return sel;
	}

	protected void editorContextMenuAboutToShow(IMenuManager menu) {
		super.editorContextMenuAboutToShow(menu);
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction");
		
		/*
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT, 
				Activator.PLUGIN_ID + ".source.menu");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				"net.sf.sveditor.ui.source.menu.as");
		 */
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT, 
				"net.sf.sveditor.ui.override.tf");
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenTypeHierarchyAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenObjectsAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenQuickObjectsAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenQuickOutlineAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenQuickHierarchyAction");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenDiagForSelectionAction");
		
		addAction(menu, ITextEditorActionConstants.GROUP_FIND,
				SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction");
		
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT,
				"net.sf.sveditor.ui.source.menu");
		
		/*
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT, 
				"net.sf.sveditor.ui.source.menu.as");
		
		IMenuManager editMenu = menu.findMenuUsingPath(
				IWorkbenchActionConstants.M_EDIT);
		
		System.out.println("editMenu=" + editMenu);
		 */
	}
	
	@Override
	public void dispose() {
		super.dispose();
		
		if (fOutline != null) {
			fOutline.dispose();
			fOutline = null;
		}
		if (fCharacterMatcher != null) {
			fCharacterMatcher.dispose();
			fCharacterMatcher = null;
		}
		
		SVCorePlugin.getDefault().getProjMgr().removeProjectSettingsListener(this);
		SVUiPlugin.getDefault().getPreferenceStore().removePropertyChangeListener(
				fPropertyChangeListener);
		
		// Remove handles to shadow index
		fSVDBIndex = null;
		fIndexMgr  = null;
	}

	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new SVSourceViewerConfiguration(this));
		
		super.createPartControl(parent);
		
		if (fHighlightManager == null) {
			fHighlightManager = new SVHighlightingManager();
			fHighlightManager.install(
					(SourceViewer)getSourceViewer(),
					(SVPresentationReconciler)getSourceViewerConfiguration().getPresentationReconciler(getSourceViewer()),
					this);
		}
		
		// Setup matching character highligher
		if (fMatchingCharacterPainter == null) {
			if (getSourceViewer() instanceof ISourceViewerExtension2) {
				fMatchingCharacterPainter = new MatchingCharacterPainter(
						getSourceViewer(), fCharacterMatcher);
				Display display = Display.getCurrent();
				
				// TODO: reference preference store
				fMatchingCharacterPainter.setColor(display.getSystemColor(SWT.COLOR_GRAY));
				((ITextViewerExtension2)getSourceViewer()).addPainter(
						fMatchingCharacterPainter);
			}
		}
		
		
		/**
		 * Add semantic highlighting
		 */
		
	}

	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public String getFilePath() {
		/*
		IEditorInput ed_in = getEditorInput();
		String ret = null;
		
		if (ed_in instanceof IFileEditorInput) {
			ret = ((IFileEditorInput)ed_in).getFile().getFullPath().toOSString();
		} else if (ed_in instanceof IURIEditorInput) {
			ret = ((IURIEditorInput)ed_in).getURI().getPath();
		}
		
		return ret;
		 */
		return fSVDBFilePath;
	}
	
	
	public void setSelection(ISVDBItemBase it, boolean set_cursor) {
		int start = -1;
		int end   = -1;
		
		if (it.getLocation() != null) {
			start = it.getLocation().getLine();
			
			if (it instanceof ISVDBScopeItem &&
					((ISVDBScopeItem)it).getEndLocation() != null) {
				end = ((ISVDBScopeItem)it).getEndLocation().getLine();
			}
			setSelection(start, end, set_cursor);
		}
	}
	
	public void setSelection(int start, int end, boolean set_cursor) {
		IDocument doc = getDocumentProvider().getDocument(getEditorInput());
		
		// Lineno is used as an offset
		if (start > 0) {
			start--;
		}
		
		if (end == -1) {
			end = start;
		}
		try {
			int offset    = doc.getLineOffset(start);
			int last_line = doc.getLineOfOffset(doc.getLength()-1);
			
			if (end > last_line) {
				end = last_line;
			}
			int offset_e = doc.getLineOffset(end);
			setHighlightRange(offset, (offset_e-offset), false);
			if (set_cursor) {
				getSourceViewer().getTextWidget().setCaretOffset(offset);
			}
			selectAndReveal(offset, 0, offset, (offset_e-offset));
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}
	
	public ISourceViewer sourceViewer() {
		return getSourceViewer();
	}
	
	/**
	 * Clears error annotations
	 */
	@SuppressWarnings("unchecked")
	private void clearErrors() {
		/*
		System.out.println("getDocumentProvider: " + getDocumentProvider());
		System.out.println("getEditorInput: " + getEditorInput());
		System.out.println("getAnnotationMode: " + getDocumentProvider().getAnnotationModel(getEditorInput()));
		 */
		if (getDocumentProvider() == null || getEditorInput() == null ||
				getDocumentProvider().getAnnotationModel(getEditorInput()) == null) {
			return;
		}
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();

		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals("org.eclipse.ui.workbench.texteditor.error")) {
				ann_model.removeAnnotation(ann);
			}
		}
	}

	/**
	 * Add error annotations from the 
	 */
	private void addErrorMarkers(List<SVDBMarker> markers) {
		// Mostly used in testing mode
		if (getDocumentProvider() == null || getEditorInput() == null ||
				getDocumentProvider().getAnnotationModel(getEditorInput()) == null) {
			return;
		}
		clearErrors();
		IAnnotationModel ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		for (SVDBMarker marker : markers) {
			Annotation ann = null;
			int line = -1;

			if (marker.getMarkerType() == MarkerType.Error) {
				ann = new Annotation(
						"org.eclipse.ui.workbench.texteditor.error", 
						false, marker.getMessage());
				line = marker.getLocation().getLine();
			}

			if (ann != null) {
				IDocument doc = getDocumentProvider().getDocument(getEditorInput());
				try {
					Position pos = new Position(doc.getLineOffset(line-1));
					ann_model.addAnnotation(ann, pos);
				} catch (BadLocationException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
	@Override
	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		if (adapter.equals(IContentOutlinePage.class)) {
			if (fOutline == null) {
				fOutline = new SVOutlinePage(this);
			}
			return fOutline;
		}
		return super.getAdapter(adapter);
	}
	
	private IPropertyChangeListener fPropertyChangeListener = 
		new IPropertyChangeListener() {

			public void propertyChange(PropertyChangeEvent event) {
				SVColorManager.clear();
				getCodeScanner().updateRules();
				getSourceViewer().getTextWidget().redraw();
				getSourceViewer().getTextWidget().update();
			}
	};

}
