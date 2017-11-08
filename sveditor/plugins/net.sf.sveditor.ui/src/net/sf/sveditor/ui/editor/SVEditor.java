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


package net.sf.sveditor.ui.editor;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.information.IInformationPresenter;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.MatchingCharacterPainter;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.custom.CaretEvent;
import org.eclipse.swt.custom.CaretListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.ITextEditorHelpContextIds;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.ide.IDEActionFactory;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.AddTaskAction;
import org.eclipse.ui.texteditor.IAbstractTextEditorHelpContextIds;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBEndLocation;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBUnprocessedRegion;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBIndexParse;
import net.sf.sveditor.core.db.index.SVDBFileOverrideIndex;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.index.SVDBIndexChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBShadowIncludeFilesFinder;
import net.sf.sveditor.core.db.index.SVDBShadowIndexParse;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.ISVDBProjectSettingsListener;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.utils.OverrideTaskFuncFinder;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.actions.AddBlockCommentAction;
import net.sf.sveditor.ui.editor.actions.AddNdocsAction;
import net.sf.sveditor.ui.editor.actions.FindReferencesAction;
import net.sf.sveditor.ui.editor.actions.GoToNextPrevElementAction;
import net.sf.sveditor.ui.editor.actions.GotoMatchingBracketAction;
import net.sf.sveditor.ui.editor.actions.IndentAction;
import net.sf.sveditor.ui.editor.actions.NextWordAction;
import net.sf.sveditor.ui.editor.actions.OpenDeclarationAction;
import net.sf.sveditor.ui.editor.actions.OpenDiagForSelectionAction;
import net.sf.sveditor.ui.editor.actions.OpenMacroExpansionAction;
import net.sf.sveditor.ui.editor.actions.OpenObjectsViewAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickHierarchyAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickObjectsViewAction;
import net.sf.sveditor.ui.editor.actions.OpenQuickOutlineAction;
import net.sf.sveditor.ui.editor.actions.OpenTypeAction;
import net.sf.sveditor.ui.editor.actions.OpenTypeHierarchyAction;
import net.sf.sveditor.ui.editor.actions.OverrideTaskFuncAction;
import net.sf.sveditor.ui.editor.actions.PrevWordAction;
import net.sf.sveditor.ui.editor.actions.RemoveBlockCommentAction;
import net.sf.sveditor.ui.editor.actions.SVMoveLinesAction;
import net.sf.sveditor.ui.editor.actions.SVRulerAnnotationAction;
import net.sf.sveditor.ui.editor.actions.SelNextWordAction;
import net.sf.sveditor.ui.editor.actions.SelPrevWordAction;
import net.sf.sveditor.ui.editor.actions.SelectEnclosingElementAction;
import net.sf.sveditor.ui.editor.actions.ToggleCommentAction;
import net.sf.sveditor.ui.editor.outline.SVOutlinePage;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

/**
 * @author C08381
 *
 */
public class SVEditor extends TextEditor 
	implements ISVDBProjectSettingsListener, ISVEditor, ILogLevel, 
			ISVDBIndexChangeListener, IResourceChangeListener,
			IPartListener, CaretListener {

	// Flag notes whether the editor is active
	private boolean							fIsOpen;

	private SVOutlinePage					fOutline;
	private SVHighlightingManager			fHighlightManager;
	private SVCodeScanner					fCodeScanner;
	private MatchingCharacterPainter		fMatchingCharacterPainter;
	private SVCharacterPairMatcher			fCharacterMatcher;
	
	// Holds the current parsed AST view of the file
	private SVDBFile						fSVDBFile;
	
	// Holds the current parsed AST pre-processor view of the file
	private SVDBFile						fSVDBFilePP;
	
	// Holds the current list of markers from the file
	private List<SVDBMarker>				fMarkers;
	
	private String							fFile;
	private IContentType					fContentType;
	
	// The FileIndexParser is responsible for parsing file content
	// in a way consistent with the containing scope
	private ISVDBIndexParse					fFileIndexParser;

	// The SVDBIndex is responsible for providing a merged view 
	// of this and the containing index to clients, including
	// content assist
	private SVDBFileOverrideIndex			fSVDBIndex;
	
	private LogHandle						fLog;
	private String							fSVDBFilePath;
	private UpdateProjectSettingsJob		fProjectSettingsJob;
	private SVDBProjectData					fPendingProjectSettingsUpdate;
	private UpdateSVDBFileJob				fUpdateSVDBFileJob;
	private boolean							fPendingUpdateSVDBFile;
	private boolean							fNeedUpdate;
	private boolean							fOccurrenceHighlightDebounceActive;
	
	private Map<String, Boolean>			fFoldingPrefs = new HashMap<String, Boolean>();
	
	private IInformationPresenter 			fQuickObjectsPresenter;
	private IInformationPresenter 			fQuickOutlinePresenter;
	private IInformationPresenter 			fQuickHierarchyPresenter;
	
	private ProjectionSupport				fProjectionSupport;
	private boolean							fInitialFolding = true;
	private int								fReparseDelay;
	private boolean							fIncrReparseEn = false;
	
	private boolean							fCaretMovedArmed = false;
	private boolean							fCaretMovedArmed2 = false;
	
	public ISVDBIndex getSVDBIndex() {
		return fSVDBIndex ;
	}
	
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
		private IDocument fDocument;
		
		public UpdateSVDBFileJob(IDocument doc) {
			super("Update SVDBFile");
			fDocument = doc;
		}

		// Note: This thread may be running after the editor exits
		// Periodic checks short-circuit this thread
		@Override
		protected IStatus run(IProgressMonitor monitor) {
			long start, end;
			IDocument doc;
			
			if (!fIsOpen) {
				return Status.OK_STATUS;
			}
			
			fLog.debug(LEVEL_MID, "--> UpdateSVDBFile.GetDocument");
			start = System.currentTimeMillis();
			IEditorInput ed_in = getEditorInput();
			if (fDocument != null) {
				doc = fDocument;
			} else {
				doc = getDocumentProvider().getDocument(ed_in);
			}
		
			if (doc == null) {
				return Status.OK_STATUS;
			}
			
			StringInputStream sin = new StringInputStream(doc.get());
			end = System.currentTimeMillis();
			fLog.debug(LEVEL_MID, "<-- UpdateSVDBFile.GetDocument: " + (end-start));
			
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			
			fLog.debug(LEVEL_MID, "--> UpdateSVDBFile.Re-parse file");
			start = System.currentTimeMillis();
//			try { Thread.sleep(10000); } catch (InterruptedException e) {}

			// Bail out if the editor has already closed
			if (!fIsOpen) {
				if (sin != null) {
					try { sin.close(); } catch (IOException e) {}
				}
				return Status.OK_STATUS;
			}
			
			Tuple<SVDBFile, SVDBFile> new_in = fFileIndexParser.parse(
					monitor, sin, fSVDBFilePath, markers);
			fSVDBFile.clearChildren();
			end = System.currentTimeMillis();
			fLog.debug(LEVEL_MID, "<-- UpdateSVDBFile.Re-parse file: " + (end-start));
			
			if (!fIsOpen) {
				return Status.OK_STATUS;
			}
		
			fLog.debug(LEVEL_MID, "--> UpdateSVDBFile.Re-incorporate content");
			start = System.currentTimeMillis();
			if (new_in != null) {
				fSVDBFile = new_in.second();
				fSVDBFilePP = new_in.first();
				if (fSVDBIndex != null) {
					fSVDBIndex.setFile(fSVDBFile);
					fSVDBIndex.setFilePP(fSVDBFilePP);
				}

				addErrorMarkers(markers);
				applyUnprocessedRegions(fSVDBFilePP);
				applyFolding(fSVDBFile, fSVDBFilePP);
				applyOverrideAnnotations(fSVDBFile);
			} else {
				fLog.debug(LEVEL_MAX, "-- UpdateSVDBFile.new_in==null");
			}
			
			if (fOutline != null) {
				fOutline.refresh();
			}
			end = System.currentTimeMillis();
			fLog.debug(LEVEL_MID, "<-- UpdateSVDBFile.Re-incorporate content: " + (end-start));
			
			synchronized (SVEditor.this) {
				start = System.currentTimeMillis();
				fLog.debug(LEVEL_MID, "--> UpdateSVDBFile.End ");
				fUpdateSVDBFileJob = null;
				fNeedUpdate = false;
				if (fPendingUpdateSVDBFile) {
					updateSVDBFile(fDocument, true);
				}
				end = System.currentTimeMillis();
				fLog.debug(LEVEL_MID, "<-- UpdateSVDBFile.End: " + (end-start));
			}
			
			return Status.OK_STATUS;
		}
	}
	
	public SVEditor() {
		super();
		
		fMarkers = new ArrayList<SVDBMarker>();
		fCodeScanner = new SVCodeScanner(null);
		
		setDocumentProvider(SVEditorDocumentProvider.getDefault());
		
		fCharacterMatcher = new SVCharacterPairMatcher();
		SVUiPlugin.getDefault().getPreferenceStore().addPropertyChangeListener(
				fPropertyChangeListener);
		
		fLog = LogFactory.getLogHandle("SVEditor");
		
		// Check in with the plug-in
		SVUiPlugin.getDefault().startRefreshJob();
		
		updateFoldingPrefs();
		updateAutoIndexDelayPref();
		
	}
	
	protected void updateAutoIndexDelayPref() {
		IPreferenceStore ps = SVUiPlugin.getDefault().getChainedPrefs();

		boolean en = ps.getBoolean(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_ENABLE);
		int delay = ps.getInt(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY);
		
		if (delay == -1) {
			en = false;
		}
	
		if (en) {
			fIncrReparseEn = true;
			fReparseDelay = delay;
		} else {
			fIncrReparseEn = false;
		}
	}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		super.init(site, input);
		
		IFile file = null;

		site.getPage().addPartListener(this);
	
		if (input instanceof IFileEditorInput) {
			ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
			fFile = ((IFileEditorInput)input).getFile().getFullPath().toOSString();
			file = ((IFileEditorInput)input).getFile();
		} else if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			if (uri.getScheme().equals("plugin")) {
				fFile = "plugin:" + uri.getPath();
			} else {
				fFile = uri.getPath();
			}
		} else if (input instanceof IStorageEditorInput) {
			IStorageEditorInput si = (IStorageEditorInput)input;
			IStorage s = null;
			try {
				s = si.getStorage();
				fFile = s.getFullPath().toOSString();
			} catch (CoreException e) {
				fLog.error("Failed to get storage for IStorageEditorInput file", e);
			}
		}
		
		if (file != null) {
			fContentType = IDE.getContentType(file);
		}
		fCodeScanner.updateRules(fContentType);

		/**
		 * Confirm that the document has an associated partitioner. If not,
		 * register the default SVEditor partitioner.
		 * Tools, such as the EGit plug-in, can request that a specific 
		 * editor be opened, but provide a filename that results in the
		 * default partitioner not being applied.
		 */
		if (getDocument() instanceof IDocumentExtension3) {
			IDocumentExtension3 docExt = (IDocumentExtension3)getDocument();
			if (docExt.getPartitionings() == null || docExt.getPartitionings().length == 0) {
				IDocumentPartitioner p = SVDocumentSetupParticipant.createPartitioner();
				docExt.setDocumentPartitioner(SVDocumentPartitions.SV_PARTITIONING, p);
				p.connect((IDocument)docExt);
			}
		}
		
		fSVDBFile = new SVDBFile(fFile);
		fSVDBFilePP = new SVDBFile(fFile);
		
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

		
//		getSelectionProvider().addSelectionChangedListener(selectionChangedListener);
		
		// Hook into the SVDB management structure
		initSVDBMgr();
		
		updateAutoIndexDelayPref();
		fIsOpen = true;
	}

	public IContentType getContentType() {
		return fContentType;
	}
	
	
	@Override
	public void doSave(IProgressMonitor progressMonitor) {

		IPreferenceStore ps = SVUiPlugin.getDefault().getPreferenceStore();
		int line_nr = 0;
		int column = 0;
		String delim = "\n";
		
		
		// Only run the following relatively expensive piece of code if we want to do any actions "onSave"
		if (ps.contains(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE) && ps.getBoolean(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE))  {
			IDocument doc = getDocument();
			
			// Figure out where we are at the moment so that we can replace the cursor close as possible to this spot
			ITextSelection sel= getTextSel();
			try {
				line_nr = doc.getLineOfOffset(sel.getOffset());
				column  = sel.getOffset() - doc.getLineOffset(line_nr);
				delim   = doc.getLineDelimiter(0);
			} catch (BadLocationException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			
			String str = doc.get();
			

			// Newline at end of file
			if (ps.contains(SVEditorPrefsConstants.P_NEWLINE_AT_END_OF_FILE) && ps.getBoolean(SVEditorPrefsConstants.P_NEWLINE_AT_END_OF_FILE))  {
				if (!str.endsWith(delim))  {
					str = str.concat(delim);
				}
			}
			
			// Strip whitespace if user elects remove it
			if (ps.contains(SVEditorPrefsConstants.P_REMOVE_TRAILING_WHITESPACE) && ps.getBoolean(SVEditorPrefsConstants.P_REMOVE_TRAILING_WHITESPACE))  {
				// Check for trailing whitespace within the file
				str = str.replaceAll("[ \\t]+" + delim, delim);
				
				// Now check for any whitespace at the end of the string
				// I believe the code below is cheaper than a regex
 				while((str.charAt(str.length()-1) == ' ') || (str.charAt(str.length()-1) == '\t'))  {
					str = str.substring(0, str.length()-1);
				}
			}
			
			// Indent if required
			if (ps.contains(SVEditorPrefsConstants.P_FORMAT_SOURCE_CODE) && ps.getBoolean(SVEditorPrefsConstants.P_FORMAT_SOURCE_CODE))  {
				// Run the indenter over the reference source
				SVIndentScanner scanner = new SVIndentScanner(new StringTextScanner(new StringBuilder(str)));
				ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
				indenter.init(scanner);

				// Indent code
				str = indenter.indent(-1, -1);
			}


			// Only modify doc and update the cursor position if something actually changed... 
			// How expensive is this check on large files?
			if (!doc.get().equals(str))  {
				
				doc.set(str);
				
				// Replace the cursor as close as possible to original spot
				int offset = 0;
				
				try {
					offset = doc.getLineOffset(line_nr);
					int linelength = doc.getLineLength(line_nr)-1;
					if (linelength > column)  {
						offset += column;
					}
					else  {
						offset += linelength;
					}
				} catch (BadLocationException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				selectAndReveal(offset, 0, offset, 0);
			}
			
		}
		
		super.doSave(progressMonitor);
	
		if (!fIncrReparseEn) {
			updateSVDBFile(getDocument(), true);
		}
		
		// TODO: When the user saves the file, clear any cached information
		// on validity.
	}

	@Override
	public void doSaveAs() {
		super.doSaveAs();
	
		if (!fIncrReparseEn) {
			updateSVDBFile(getDocument(), true);
		}
		
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
				String pname = (data != null)?data.getName():null;
				fProjectSettingsJob = new UpdateProjectSettingsJob(this, pname);
				fProjectSettingsJob.schedule();
				fPendingProjectSettingsUpdate = null;
			} else {
				fPendingProjectSettingsUpdate = data;
			}
		}
	}

	public void int_projectSettingsUpdated(
			final ISVDBIndex 		index, 
			SVDBIndexCollection 	index_mgr) {
		fLog.debug(LEVEL_MIN, "projectSettingsUpdated " + fSVDBFilePath + " - index=" + 
				((index != null)?(index.getTypeID() + "::" + index.getBaseLocation()):"null") + 
				" ; index_mgr=" + 
				((index_mgr != null)?(index_mgr.getProject()):"null"));
		
		final SVActionContributor ac = (SVActionContributor)getEditorSite().getActionBarContributor();
		getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
			public void run() {
				String msg = "";
				boolean is_indexed = false;
				if (index != null) {
					msg = "Index: " + index.getBaseLocation();
					is_indexed = true;
				} else {
					msg = "Index: None";
				}
				ac.getActionBars().getStatusLineManager().setMessage(msg);
				Image icon = null;
				if (is_indexed) {
					icon = SVUiPlugin.getImage("/icons/vlog_16_16_indexed.gif");
				} else {
					icon = SVUiPlugin.getImage("/icons/vlog_16_16.gif");
				}
				setTitleImage(icon);
			}
		});
		
		synchronized (this) {
			fProjectSettingsJob = null;
			
			if (index == null) {
				// Create a shadow index
				
				// See if this file is part of a project with a
				// configured index
				IFile file = SVFileUtils.findWorkspaceFile(fSVDBFilePath);
				String file_dir = SVFileUtils.getPathParent(fSVDBFilePath);
				
				if (file != null) {
					if (SVDBProjectManager.isSveProject(file.getProject())) {
						SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
						SVDBProjectData pdata = pmgr.getProjectData(file.getProject());
					
						if (pdata != null) {
							index_mgr = pdata.getProjectIndexMgr();
						}
					}
				}
			
				fFileIndexParser = new SVDBShadowIndexParse(index_mgr);
				fSVDBIndex = new SVDBFileOverrideIndex(
						fSVDBFile, fSVDBFilePP, index, index_mgr, fMarkers);
				fSVDBIndex.setIncFilesFinder(
						new SVDBShadowIncludeFilesFinder(file_dir));
				fLog.debug(LEVEL_MIN, "init w/ShadowIndex");
			} else {
				// An index was specified, so proceed normally
				
				// Unhook the index listener from the old index
				ISVDBIndex old_index = null;
				if (fSVDBIndex != null) {
					old_index = fSVDBIndex.getBaseIndex();
				}
				if (old_index != null) {
					old_index.removeChangeListener(this);
				}
			
				// Add a change listener to the new index
				index.addChangeListener(this);
				
				fFileIndexParser = index_mgr;
				fSVDBIndex = new SVDBFileOverrideIndex(
						fSVDBFile, fSVDBFilePP, index, index_mgr, fMarkers);
				fLog.debug(LEVEL_MIN, "init w/RealIndex");
			}
		}
		if (fPendingProjectSettingsUpdate != null) {
			projectSettingsChanged(fPendingProjectSettingsUpdate);
		} else {
			updateSVDBFile(null, false);
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
				
				fFileIndexParser = new SVDBIndexCollection(rgy.getIndexCollectionMgr(), plugin);

				// TODO: This argues that we should have an index collection
				// for each plugin index 
				/*
				if (target != null) {
					fLog.debug(LEVEL_MIN, "Found a target plugin library");
					fIndexMgr.addPluginLibrary(rgy.findCreateIndex(
							new NullProgressMonitor(), 
							SVDBIndexRegistry.GLOBAL_PROJECT, target.getId(), 
							SVDBPluginLibIndexFactory.TYPE, null));
				} else {
					fLog.debug(LEVEL_MIN, "Did not find the target plugin library");
				}
				 */
			} else { // regular workspace or filesystem path
				if (ed_in instanceof FileEditorInput) {
					// Regular in-workspace file
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
					// Outside-workspace file
					fLog.debug(LEVEL_MIN, "URI instance: " + uri_in.getClass().getName());
					fSVDBFilePath = SVFileUtils.normalize(uri_in.getURI().getPath());
					fLog.debug(LEVEL_MIN, "Normalizing file \"" + uri_in.getURI().getPath() + "\" to \"" + fSVDBFilePath + "\"");
					fLog.debug(LEVEL_MIN, "File \"" + fSVDBFilePath + "\" is outside the workspace");

					// Kick off a job to find the relevant index
					projectSettingsChanged(null);
				}
			}
		} else {
			fLog.error("SVEditor input is of type " + ed_in.getClass().getName());
		}
	}

	void updateSVDBFile(IDocument doc, boolean force) {
		fLog.debug(LEVEL_MAX, "updateSVDBFile - fIndexMgr=" + fFileIndexParser);
	
		if (fFileIndexParser != null) {
			if (fUpdateSVDBFileJob == null) {
				synchronized (this) {
					fPendingUpdateSVDBFile = false;
					if (fIncrReparseEn || force) {
						fUpdateSVDBFileJob = new UpdateSVDBFileJob(doc);
						fUpdateSVDBFileJob.schedule(fReparseDelay);
					}
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
		
		OpenMacroExpansionAction me_action = new OpenMacroExpansionAction(bundle, this);
		me_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.macro.expansion");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenMacroExpansionAction",  me_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenMacroExpansionAction", true);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svOpenMacroExpansionAction", true);
		
		
		FindReferencesAction fr_action = new FindReferencesAction(bundle, this);
		fr_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.find.references");
		setAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", fr_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svFindReferencesAction", false);
		
		OpenTypeAction ot_action = new OpenTypeAction(bundle, this);
		ot_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".editor.open.type");
		setAction(SVUiPlugin.PLUGIN_ID + ".svOpenTypeAction", ot_action);
		
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
		
		GotoMatchingBracketAction goto_mb_action = new GotoMatchingBracketAction(
				bundle, "GotoMatchingBracket.", this);
		goto_mb_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".gotoMatchingBracket");
		setAction(SVUiPlugin.PLUGIN_ID + ".gotoMatchingBracket", goto_mb_action);
		
		SelectEnclosingElementAction sel_ee_action = new SelectEnclosingElementAction(
				bundle, "SelectEnclosingElement.", this);
		sel_ee_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".SelectEnclosingElement");
		setAction(SVUiPlugin.PLUGIN_ID + ".SelectEnclosingElement", sel_ee_action);
		
		GoToNextPrevElementAction sel_ne_action = new GoToNextPrevElementAction(
				bundle, "GoToNextElement.", this, true);
		sel_ne_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".GoToNextElement");
		setAction(SVUiPlugin.PLUGIN_ID + ".GoToNextElement", sel_ne_action);
		
		GoToNextPrevElementAction sel_pe_action = new GoToNextPrevElementAction(
				bundle, "GoToPrevElement.", this, false);
		sel_pe_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".GoToPrevElement");
		setAction(SVUiPlugin.PLUGIN_ID + ".GoToPrevElement", sel_pe_action);
		
		AddNdocsAction add_ndocs_action = new AddNdocsAction(
				bundle, "Add NDOCS Action.", this, false);
		add_ndocs_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".AddNdocsAction");
		setAction(SVUiPlugin.PLUGIN_ID + ".AddNdocsAction", add_ndocs_action);
		
		// Add annotation-action
		SVRulerAnnotationAction action = new SVRulerAnnotationAction(bundle, 
				"Editor.RulerAnnotationSelection.", this, getVerticalRuler());
		setAction(ITextEditorActionConstants.RULER_CLICK, action);
	
		SVMoveLinesAction move_action;
//		org.eclipse.ui.texteditor.EditorMessages.getBundleForConstructedKeys();
		move_action = new SVMoveLinesAction(
				bundle, "Editor.MoveLinesUp.", this, getSourceViewer(), true, false); 
		move_action.setHelpContextId(IAbstractTextEditorHelpContextIds.MOVE_LINES_ACTION);
		move_action.setActionDefinitionId(ITextEditorActionDefinitionIds.MOVE_LINES_UP);
		setAction(ITextEditorActionConstants.MOVE_LINE_UP, move_action);
		
		move_action = new SVMoveLinesAction(
				bundle, "Editor.MoveLinesDown.", this, getSourceViewer(), false, false); 
		move_action.setHelpContextId(IAbstractTextEditorHelpContextIds.MOVE_LINES_ACTION);
		move_action.setActionDefinitionId(ITextEditorActionDefinitionIds.MOVE_LINES_DOWN);
		setAction(ITextEditorActionConstants.MOVE_LINE_DOWN, move_action);
		
	}
	
	public ISVDBIndexIterator getIndexIterator() {
		return fSVDBIndex;
	}
	
	public ISVStringPreProcessor createPreProcessor(int limit_lineno) {
		IDocument doc = getDocument();
		StringInputStream sin = new StringInputStream(doc.get());
	
		return fFileIndexParser.createPreProc(getFilePath(), sin, limit_lineno);
	}
	
	public IDocument getDocument() {
		return getDocumentProvider().getDocument(getEditorInput());
	}
	
	public IAnnotationModel getAnnotationModel() {
		IAnnotationModel ann_model = null;
		
		ann_model = getDocumentProvider().getAnnotationModel(getEditorInput());
		
		return ann_model;
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
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenMacroExpansionAction");
		
		/*
		addGroup(menu, ITextEditorActionConstants.GROUP_EDIT, 
				Activator.PLUGIN_ID + ".source.menu");
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				"net.sf.sveditor.ui.source.menu.as");
		 */
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT, 
				"net.sf.sveditor.ui.override.tf");
		
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svOpenTypeAction");
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
	
		fIsOpen = false;
		
		getSite().getPage().removePartListener(this);
		
		if (fOutline != null) {
			fOutline.dispose();
			fOutline = null;
		}
		if (fCharacterMatcher != null) {
			fCharacterMatcher.dispose();
			fCharacterMatcher = null;
		}

		if (getSelectionProvider() != null) {
			getSelectionProvider().removeSelectionChangedListener(selectionChangedListener);
		}
		
		SVCorePlugin.getDefault().getProjMgr().removeProjectSettingsListener(this);
		SVUiPlugin.getDefault().getPreferenceStore().removePropertyChangeListener(
				fPropertyChangeListener);
		
		// Remove handles to shadow index
		fSVDBIndex = null;
		fFileIndexParser  = null;

		// Remove the resource listener
		ResourcesPlugin.getWorkspace().addResourceChangeListener(this);
	}
	
	public SVSourceViewerConfiguration getSourceViewerConfig() {
		return (SVSourceViewerConfiguration)getSourceViewerConfiguration();
	}
	
	public ITextViewer getTextViewer() {
		return (ITextViewer)getSourceViewer();
	}

	public void createPartControl(Composite parent) {
		
		setSourceViewerConfiguration(new SVSourceViewerConfiguration(this,SVUiPlugin.getDefault().getPreferenceStore()));
		
		super.createPartControl(parent);
		
	    ProjectionViewer viewer = (ProjectionViewer)getSourceViewer();

	    fProjectionSupport = new ProjectionSupport(viewer, getAnnotationAccess(), getSharedColors());
	    fProjectionSupport.install();
	    
	    //turn projection mode on
	    if (getFoldingPref(SVEditorPrefsConstants.P_FOLDING_ENABLE)) {
	    	viewer.doOperation(ProjectionViewer.TOGGLE);
	    }
	    
		if (fHighlightManager == null) {
			fHighlightManager = new SVHighlightingManager();
			fHighlightManager.install(
					(SourceViewer)getSourceViewer(),
					(SVPresentationReconciler)getSourceViewerConfiguration().getPresentationReconciler(getSourceViewer()),
					this);
		}
		
		// Setup matching character highlighter
		if (fMatchingCharacterPainter == null) {
			if (getSourceViewer() instanceof ISourceViewerExtension2) {
				fMatchingCharacterPainter = new MatchingCharacterPainter(
						getSourceViewer(), fCharacterMatcher);
				
				fMatchingCharacterPainter.setColor(SVEditorColors.getColor(SVEditorColors.MATCHING_BRACE));
				((ITextViewerExtension2)getSourceViewer()).addPainter(
						fMatchingCharacterPainter);
			}
		}
		
		getSourceViewer().getSelectionProvider().addSelectionChangedListener(selectionChangedListener);
		
		/**
		 * Add semantic highlighting
		 */
	
		getSourceViewer().getTextWidget().addCaretListener(this);
	}
	
	private Runnable fCaretMovedRunnable = new Runnable() {
		
		@Override
		public void run() {
			if (fCaretMovedArmed2) {
				fCaretMovedArmed2 = false;
			} else {
				if (fOutline != null) {
					fOutline.updateCursorLocation(getSourceViewer().getTextWidget().getCaretOffset());
				}
				fCaretMovedArmed = false;
				fCaretMovedArmed2 = false;
			}
		}
	};
	
	@Override
	public void caretMoved(CaretEvent event) {
		if (!fCaretMovedArmed) {
			Display.getDefault().timerExec(500, fCaretMovedRunnable);
		} else {
			fCaretMovedArmed2 = true;
		}
	}

	@Override
	protected ISourceViewer createSourceViewer(
			Composite 			parent,
			IVerticalRuler 		ruler, 
			int 				styles) {
		ISourceViewer viewer = new ProjectionViewer(parent, ruler,
				getOverviewRuler(), isOverviewRulerVisible(), styles);

		// ensure decoration support has been created and configured.
		getSourceViewerDecorationSupport(viewer);

		return viewer;		
	}

	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public SVDBFile getSVDBFilePP() {
		return fSVDBFilePP;
	}
	
	public List<SVDBFilePath> getSVDBFilePath() {
		if (fSVDBIndex != null) {
			return fSVDBIndex.getFilePath(fSVDBFilePath);
		} else {
			return null;
		}
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
		
		if (it.getLocation() != -1) {
			start = SVDBLocation.unpackLineno(it.getLocation());
			
			if (it instanceof ISVDBScopeItem &&
					((ISVDBScopeItem)it).getEndLocation() != -1) {
				end = SVDBLocation.unpackLineno(((ISVDBScopeItem)it).getEndLocation());
			}
			setSelection(start, end, set_cursor);
		}
	}
	
	
	/**
	 * @param start - start offset
	 * @param end - end offset (set to -1 to have no selection)
	 * @param set_cursor
	 */
	public void setSelection(int start, int end, boolean set_cursor) {
		IDocument doc = getDocumentProvider().getDocument(getEditorInput());
		
		// Lineno is used as an offset
		if (start > 0) {
			start--;
		}
		
		if (end == -1) {
			end = start;
		}
	
		// Mark the current location
		markInNavigationHistory();
		
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
	
	@Override
	public void index_event(SVDBIndexChangeEvent e) {
		if (e.getType() == SVDBIndexChangeEvent.Type.FullRebuild) {
			if (Display.getDefault() == null) {
				fNeedUpdate = true;
				return;
			}
			
			// Force a rebuild to pick up latest errors
			// Note: isPartVisible() is a display-thread protected method
			Display.getDefault().asyncExec(new Runnable() {
				public void run() {
					if (getSite() != null && getSite().getPage().isPartVisible(SVEditor.this)) {
						if (fSVDBIndex.getBaseIndex() == null) {
							// Try re-checking
							projectSettingsChanged(null);
						}
						updateSVDBFile(getDocument(), false);
					} else {
						// Store the knowledge that we need an update for later
						fNeedUpdate = true;
					}
				}
			});			
		}
	}

	// IPartListener methods
	public void partActivated(IWorkbenchPart part) {
		if (fNeedUpdate) {
			updateSVDBFile(getDocument(), true);
		}
	}

	public void partBroughtToTop(IWorkbenchPart part) { }
	public void partClosed(IWorkbenchPart part) { }
	public void partDeactivated(IWorkbenchPart part) { }
	public void partOpened(IWorkbenchPart part) { }

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
		ProjectionAnnotationModel ann_model = (ProjectionAnnotationModel)getDocumentProvider().getAnnotationModel(getEditorInput());
		
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		List<Annotation> remove_ann = new ArrayList<Annotation>();

		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals("org.eclipse.ui.workbench.texteditor.error")) {
				remove_ann.add(ann);
			}
		}
		ann_model.modifyAnnotations(remove_ann.toArray(new Annotation[remove_ann.size()]), 
				new HashMap<>(), new Annotation[0]);
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
		AnnotationModel ann_model = 
				(AnnotationModel)getDocumentProvider().getAnnotationModel(getEditorInput());
		
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		List<Annotation> remove_ann = new ArrayList<Annotation>();
		Map<Annotation, Position> add_ann = new HashMap<Annotation, Position>();

		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals("org.eclipse.ui.workbench.texteditor.error")) {
				remove_ann.add(ann);
			}
		}
		
		IDocument doc = getDocumentProvider().getDocument(getEditorInput());

		for (SVDBMarker marker : markers) {			
			if (marker.getMarkerType() == MarkerType.Error) {
				Annotation ann = new Annotation(
						"org.eclipse.ui.workbench.texteditor.error", 
						false, marker.getMessage());
				int line = SVDBLocation.unpackLineno(marker.getLocation());
				try {
					Position pos = new Position(doc.getLineOffset(line-1));
					add_ann.put(ann, pos);
				} catch (BadLocationException e) {
					e.printStackTrace();
				}
			}
		}
		
		ann_model.replaceAnnotations(
				remove_ann.toArray(new Annotation[remove_ann.size()]), 
				add_ann); 
	}
	
	private void applyUnprocessedRegions(SVDBFile file_pp) {
		List<SVDBUnprocessedRegion> unprocessed_regions = new ArrayList<SVDBUnprocessedRegion>();
		IDocument doc = getDocument();
		AnnotationModel ann_model = 
				(AnnotationModel)getDocumentProvider().getAnnotationModel(getEditorInput());
		
		List<Annotation> remove_ann = new ArrayList<Annotation>();
		Map<Annotation, Position> add_ann = new HashMap<Annotation, Position>();
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			
			if (ann.getType().equals("net.sf.sveditor.ui.disabledRegion")) {
				remove_ann.add(ann);
			}
		}		
		collectUnprocessedRegions(unprocessed_regions, file_pp);
		
		for (SVDBUnprocessedRegion r : unprocessed_regions) {
			long start = r.getLocation();
			long end = r.getEndLocation();

			if (start == -1 || end == -1) {
				continue;
			}
			
			int start_l = SVDBLocation.unpackLineno(start);
			int end_l = SVDBLocation.unpackLineno(end);
			Annotation ann_1 = new Annotation(SVUiPlugin.PLUGIN_ID + ".disabledRegion", false, "");
			try {
				int line1 = doc.getLineOffset((start_l>0)?start_l-1:0);
				int line2 = doc.getLineOffset(end_l);
				add_ann.put(ann_1, new Position(line1, (line2-line1)));
			} catch (BadLocationException e) {}
		}
		
		ann_model.replaceAnnotations(
				remove_ann.toArray(new Annotation[remove_ann.size()]), 
				add_ann);
	}
	
	private void collectUnprocessedRegions(List<SVDBUnprocessedRegion> unprocessed_regions, ISVDBChildParent scope) {
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (ci.getType() == SVDBItemType.UnprocessedRegion) {
				unprocessed_regions.add((SVDBUnprocessedRegion)ci);
			}
		}
	}

	@SuppressWarnings("unchecked")
	private void applyOverrideAnnotations(SVDBFile file) {
		// First, clear existing override annotations
		ISourceViewer sv = getSourceViewer();
		if (sv == null) {
			return;
		}
		AnnotationModel ann_model = (AnnotationModel)sv.getAnnotationModel();
		IDocument doc = getDocument();
		
		if (ann_model == null) {
			return;
		}
		
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		List<Annotation> remove_ann = new ArrayList<Annotation>();
		Map<Annotation, Position> add_ann = new HashMap<Annotation, Position>();
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals(SVUiPlugin.PLUGIN_ID + ".methodOverride")) {
				remove_ann.add(ann);
			}
		}
	
		OverrideTaskFuncFinder finder = new OverrideTaskFuncFinder();
		List<Tuple<SVDBTask,SVDBTask>> override_tasks = finder.find(fSVDBFile, getIndexIterator());
		
		for (Tuple<SVDBTask, SVDBTask> t : override_tasks) {
			SVDBTask tf = t.first();
			SVDBTask target_t = t.second();
			Annotation ann = new SVOverrideMethodAnnotation(target_t, 
					"overrides " + SVDBItem.getName(target_t.getParent()) + "::" + target_t.getName());
			
			try {
				int line = SVDBLocation.unpackLineno(tf.getLocation());
				if (line > 0) {
					line = doc.getLineOffset(line-1);
				} else {
					line = doc.getLineOffset(0);
				}
				add_ann.put(ann, new Position(line, 0));
			} catch (BadLocationException e) {
				e.printStackTrace();
			}			
		}
		
		ann_model.replaceAnnotations(
				remove_ann.toArray(new Annotation[remove_ann.size()]), 
				add_ann); 
	}
	
	@SuppressWarnings("rawtypes")
	private Annotation [] computeDifferences(ProjectionAnnotationModel model, List<Tuple<Position, Boolean>> regions) {
		List<Annotation> deletions = new ArrayList<Annotation>();

		Iterator ann_it = model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Object ann_o = ann_it.next();
			
			if (ann_o instanceof ProjectionAnnotation) {
				ProjectionAnnotation ann_p = (ProjectionAnnotation)ann_o;
				Position pos = model.getPosition(ann_p);
				
				// See if this already exists
				int idx = -1;
				for (int i=0; i<regions.size(); i++) {
					Tuple<Position, Boolean> tr = regions.get(i);
					// The annotation model attempts to update the bounds of the projection
					// annotation when the document changes. It mostly successful, but 
					// seems to get tripped up when pasting or deleting a block of content
					// from within an folding region. Work around this by recognizing that
					// a region that starts at the same point is the same even if the
					// length has changed.
					if (tr.first().equals(pos) ||
							tr.first().getOffset() == pos.getOffset()) {
						idx = i;
						break;
					}
				}
				
				if (idx != -1) {
					regions.remove(idx);
				} else {
					deletions.add(ann_p);
				}
			}
		}
		
		return deletions.toArray(new Annotation[deletions.size()]);
	}
	
	public ProjectionAnnotationModel getProjectionAnnotationModel() {
		return ((ProjectionViewer)getSourceViewer()).getProjectionAnnotationModel();
	}
	
	private void applyFolding(SVDBFile file, SVDBFile file_pp) {
	    ProjectionViewer viewer =(ProjectionViewer)getSourceViewer();
	    if (viewer == null) {
	    	return;
	    }
	    ProjectionAnnotationModel ann_model = viewer.getProjectionAnnotationModel();
	    
	    if (ann_model == null) {
	    	return;
	    }
	    
		List<Tuple<Position, Boolean>> positions = 
				new ArrayList<Tuple<Position,Boolean>>();
		HashMap<ProjectionAnnotation, Position> newAnnotations = new HashMap<ProjectionAnnotation, Position>();
		
		IDocument doc = getDocument();
		
		collectFoldingRegions(SVDBLocation.unpackFileId(file.getLocation()), file, positions);
		collectMultiLineCommentFoldingRegions(doc, positions);
		
		for (ISVDBChildItem ci : file_pp.getChildren()) {
			if (ci.getType() == SVDBItemType.UnprocessedRegion) {
				SVDBUnprocessedRegion ur = (SVDBUnprocessedRegion)ci;
				long start = ur.getLocation();
				long end = ur.getEndLocation();
			
				if (start != -1 && end != -1) {
					try {
						int start_l = SVDBLocation.unpackLineno(start);
						int end_l = SVDBLocation.unpackLineno(end); // this is the `endif or `else
						
						if (start_l > 0) {
							start_l--;
						}
					
						// We want to show the ending directive
						end_l--;
						
						if (start_l < end_l) {
							int start_o = doc.getLineOffset(start_l);
							int end_o = doc.getLineOffset(end_l);
							
							boolean init_folded = false;
							
							if (fInitialFolding) {
								init_folded = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_UNPROCESSED);
							}
							
							positions.add(new Tuple<Position, Boolean>(
									new Position(start_o, (end_o-start_o)), init_folded));
									
						}
					} catch (BadLocationException e) {}
				}
			}
		}
		
		// Add folding regions for 
	
		Annotation deletions[] = computeDifferences(ann_model, positions);
		
		Annotation annotations[] = new Annotation[positions.size()];
		
		for (int i=0; i<positions.size(); i++) {
			Tuple<Position, Boolean> pos = positions.get(i);
			ProjectionAnnotation ann = new ProjectionAnnotation(pos.second());
			newAnnotations.put(ann, pos.first());
			annotations[i] = ann;
		}

		if (deletions.length != 0 || newAnnotations.size() != 0) {
			ann_model.modifyAnnotations(deletions, newAnnotations, 
					new Annotation[] {});
		}
		
		fInitialFolding = false;
	}
	
	private static final Set<SVDBItemType>				fFoldingRegions;
	private static final Set<SVDBItemType>				fRecurseFoldingRegions;
	
	static {
		fFoldingRegions = new HashSet<SVDBItemType>();
		fRecurseFoldingRegions = new HashSet<SVDBItemType>();
		fFoldingRegions.add(SVDBItemType.ModuleDecl);
		fRecurseFoldingRegions.add(SVDBItemType.ModuleDecl);
		fFoldingRegions.add(SVDBItemType.InterfaceDecl);
		fRecurseFoldingRegions.add(SVDBItemType.InterfaceDecl);
		fFoldingRegions.add(SVDBItemType.ClassDecl);
		fRecurseFoldingRegions.add(SVDBItemType.ClassDecl);
		fFoldingRegions.add(SVDBItemType.PackageDecl);
		fRecurseFoldingRegions.add(SVDBItemType.PackageDecl);
		fFoldingRegions.add(SVDBItemType.ProgramDecl);
		fRecurseFoldingRegions.add(SVDBItemType.ProgramDecl);
		
		fFoldingRegions.add(SVDBItemType.Task);
		fFoldingRegions.add(SVDBItemType.Function);
		fFoldingRegions.add(SVDBItemType.Constraint);
	}
	
	private void collectFoldingRegions(
			int 							file_id, 
			ISVDBChildParent 				scope, 
			List<Tuple<Position,Boolean>>	positions) {
		IDocument doc = getDocument();
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (fFoldingRegions.contains(ci.getType())) {
				ISVDBEndLocation el = (ISVDBEndLocation)ci;
				long start = ci.getLocation();
				long end = el.getEndLocation();
			
				if (start != -1 && end != -1) {
					int it_file_id = SVDBLocation.unpackFileId(start);
					
					if (file_id == -1 || it_file_id == file_id) {
						try {
							int start_l = SVDBLocation.unpackLineno(start);
							int end_l = SVDBLocation.unpackLineno(end);
							if (start_l != end_l) {
								if (start_l > 0) {
									start_l--;
								}

								int start_o = doc.getLineOffset(start_l);
								int end_o = doc.getLineOffset(end_l);
								
								boolean fold_default = false;
							
								if (fInitialFolding) {
									switch (ci.getType()) {
									case ModuleDecl:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_MODULES);
										break;
									case ClassDecl:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_CLASSES);
										break;
									case InterfaceDecl:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_INTERFACES);
										break;
										
									case Task:
									case Function:
										fold_default = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_TF);
										break;
									default:
										break;
									}
								}

								positions.add(new Tuple<Position, Boolean>(
										new Position(start_o, (end_o-start_o)),
										fold_default));
							}
						} catch (BadLocationException e) {}
						
						if (fRecurseFoldingRegions.contains(ci.getType())) {
							// Must recurse
							collectFoldingRegions(file_id, (ISVDBChildParent)ci, positions);
						}
					}
				}
			}
		}
	}
	
	private void collectMultiLineCommentFoldingRegions(
			IDocument 						doc,
			List<Tuple<Position,Boolean>>	positions) {

		if (doc instanceof IDocumentExtension3) {
			IDocumentExtension3 doc_ext = (IDocumentExtension3)doc;
			boolean is_first_region = true;
			
			for (int offset=0; offset<doc.getLength(); ) {
				ITypedRegion r = null;

				try {
					r = doc_ext.getPartition(
							SVDocumentPartitions.SV_PARTITIONING, offset, false);
				} catch (BadPartitioningException e) {
					e.printStackTrace();
				} catch (BadLocationException e) {
					e.printStackTrace();
				}

				if (r != null) {
					boolean init_folded = false;
				
					// Look for a header comment
					if (fInitialFolding) {
						if (is_first_region && !r.getType().equals(SVDocumentPartitions.SV_MULTILINE_COMMENT)) {
							// Check to see if the first partition is just whitespace
							is_first_region = isPartitionAllWhitespace(doc, r);
						}
					}
					
					if (r.getType().equals(SVDocumentPartitions.SV_MULTILINE_COMMENT)) {
						if (fInitialFolding) {
							if (is_first_region) {
								init_folded = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_HEADER_COMMENTS);
							} else {
								init_folded = getFoldingPref(SVEditorPrefsConstants.P_FOLDING_INIT_BLOCK_COMMENTS);
							}
							is_first_region = false;
						}

						positions.add(new Tuple<Position, Boolean>(
								new Position(r.getOffset(), r.getLength()), init_folded));
					}
					offset += r.getLength();
				} else {
					offset++;
				}
			}
		}
	}
	
	private boolean isPartitionAllWhitespace(IDocument doc, ITypedRegion r) {
		for (int i=0; i<r.getLength(); i++) {
			try {
				int ch = doc.getChar(r.getOffset()+i);
				if (!Character.isWhitespace(ch)) {
					return false;
				}
			} catch (BadLocationException e) {}
		}
	
		return true;
	}
	
	private void updateWordSelectionHighlight() {
		if (getSourceViewer() == null) {
			return;
		}
		ISelectionProvider sel_p = getSourceViewer().getSelectionProvider();
		
		if (sel_p == null) {
			return;
		}
		
		ITextSelection sel = (ITextSelection)sel_p.getSelection();
		AnnotationModel ann_model = (AnnotationModel)getDocumentProvider().getAnnotationModel(getEditorInput());
		
		List<Annotation> remove_ann = new ArrayList<Annotation>();
		Map<Annotation, Position> add_ann = new HashMap<Annotation, Position>();
		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			if (ann.getType().equals("net.sf.sveditor.ui.occurrences")) {
				remove_ann.add(ann);
			}
		}		
		
		if (sel.getText() != null && !sel.getText().trim().equals("")) {
			boolean single_word = true;
			
			for (int i=0; i<sel.getText().length(); i++) {
				char ch = sel.getText().charAt(i);
				if (Character.isWhitespace(ch)) {
					single_word = false;
					break;
				}
			}
			
			if (single_word) {
				IDocument doc = getDocumentProvider().getDocument(getEditorInput());
				FindReplaceDocumentAdapter finder = new FindReplaceDocumentAdapter(doc);
				
				// Iterate through the document
				int start = 0;
				while (true) {
					IRegion region = null;
					
					try {
						String selected_text = SVUiPlugin.shouldEscapeFindWordPattern() ? 
								Pattern.quote(sel.getText()) : sel.getText();
						region = finder.find(start, selected_text, true, true, true, false);
					} catch (BadLocationException e) {}
					
					if (region != null) {
						Annotation ann = new Annotation(
								"net.sf.sveditor.ui.occurrences",
								false, "");
						Position position = new Position(region.getOffset(), region.getLength());
						add_ann.put(ann, position);
						
						start = region.getOffset()+region.getLength();
					} else {
						break;
					}
				}
			}
		}
		ann_model.replaceAnnotations(
				remove_ann.toArray(new Annotation[remove_ann.size()]), 
				add_ann);
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
	

	private void updateFoldingPrefs() {
		fFoldingPrefs.clear();
		IPreferenceStore ps = SVUiPlugin.getDefault().getChainedPrefs();
		for (String fp : SVEditorPrefsConstants.P_FOLDING_PREFS) {
			fFoldingPrefs.put(fp, ps.getBoolean(fp));
		}
	}
	
	private boolean getFoldingPref(String key) {
		if (fFoldingPrefs.containsKey(key)) {
			return fFoldingPrefs.get(key);
		} else {
			return false;
		}
	}
	
	private IPropertyChangeListener fPropertyChangeListener = 
		new IPropertyChangeListener() {

			public void propertyChange(PropertyChangeEvent event) {
				SVColorManager.clear();
				getCodeScanner().updateRules(fContentType);
				if (getSourceViewer() != null && getSourceViewer().getTextWidget() != null) {
					getSourceViewer().getTextWidget().redraw();
					getSourceViewer().getTextWidget().update();
				}
				
				if (SVEditorPrefsConstants.P_FOLDING_PREFS.contains(event.getProperty())) {
					updateFoldingPrefs();
				} else if (event.getProperty().equals(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY) ||
						event.getProperty().equals(SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_ENABLE)) {
					updateAutoIndexDelayPref();
				}
			}
	};
	
	private ISelectionChangedListener selectionChangedListener = 
			new ISelectionChangedListener() {
				
		public void selectionChanged(SelectionChangedEvent event) {
			if (event.getSelection() instanceof ITextSelection) {
				if (!fOccurrenceHighlightDebounceActive) {
					fOccurrenceHighlightDebounceActive = true;
					Display.getDefault().timerExec(500, occurrenceHighlightDebounce);
				}
			}
		}
	};
	
	private Runnable occurrenceHighlightDebounce = new Runnable() {
		
		public void run() {
			fOccurrenceHighlightDebounceActive = false;
			updateWordSelectionHighlight();
		}
	};

	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getResource() != null && 
				event.getResource().getFullPath().toOSString().equals(fFile)) {
			// Re-parse the file and update markers if the file changes 
			// outside the editor. 
			updateSVDBFile(getDocument(), true);
		}
	}
	
}
