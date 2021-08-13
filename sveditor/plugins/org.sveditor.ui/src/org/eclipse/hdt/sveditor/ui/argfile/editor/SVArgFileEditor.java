/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.argfile.editor;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ResourceBundle;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IPathVariableChangeEvent;
import org.eclipse.core.resources.IPathVariableChangeListener;
import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileLexer;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileParser;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileUtils;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker.MarkerType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFilePath;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexUtil;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;
import org.eclipse.hdt.sveditor.ui.argfile.editor.actions.OpenDeclarationAction;
import org.eclipse.hdt.sveditor.ui.argfile.editor.outline.SVArgFileOutlinePage;
import org.eclipse.hdt.sveditor.ui.editor.actions.ToggleCommentAction;

public class SVArgFileEditor extends TextEditor 
		implements ILogLevel, IPathVariableChangeListener {
	private SVArgFileCodeScanner			fCodeScanner;
	private LogHandle						fLog;
	private UpdateSVDBFileJob				fUpdateSVDBFileJob;
	private boolean							fPendingUpdateSVDBFile;
	private String							fFile;
	private SVDBFile						fSVDBFile;
	private SVArgFileOutlinePage			fOutline;
	private ISVDBFileSystemProvider			fFSProvider;
	private boolean							fDebugEn = true;
	private IPathVariableManager			fPathVariableMgr;
	
	public SVArgFileEditor() {
		fLog = LogFactory.getLogHandle("SVArgFileEditor");
		fCodeScanner = new SVArgFileCodeScanner();
	}
	
	@Override
	public void init(IEditorSite site, IEditorInput input)
			throws PartInitException {
		super.init(site, input);
		IFile ws_file = null;
	
		if (input instanceof IFileEditorInput) {
			ws_file = ((IFileEditorInput)input).getFile();
			fFile = "${workspace_loc}" + ws_file.getFullPath().toOSString();
		} else if (input instanceof IURIEditorInput) {
			URI uri = ((IURIEditorInput)input).getURI();
			if (uri.getScheme().equals("plugin")) {
				fFile = "plugin:" + uri.getPath();
			} else {
				// Bug 280: Variable Resolution in .f file 
				// 
				// The heart of the problem is the code below, where the project name is at the
				// start of the path of "input", but the explosion, and collapse of "getURI" results in a workspace
				// path, to the highest project in the workspace, resulting in problems when you have a submodule
				// project, in the same file-system hierarchy as another project (say a chip)
				// The following code "fixes" the problem, but I don't know enough about it to really know what the 
				// greater impact of the hack is.
				// fFile = input.toString();
				// fFile = "${workspace_loc}/" + fFile .substring(fFile .indexOf("/")+1);
				// fFile = fFile .replace(")", "");
				// 
				// An alternative solution, likely better is to extract just the project name here, and pass that to "findWorkspaceFile" below,
				// which will give "findWorkspacePath" the information needed to return the "correct" path
				// String project_loc = input.toString();
				// project_loc = project_loc.substring(project_loc.indexOf("/")+1);	// remove everything to the first /
				// project_loc = project_loc.replaceAll("/.*", "");
				
				// Offending code
				fFile = SVFileUtils.normalize(uri.getPath()); 		// SGD - creates an absolute path
				
				ws_file = SVFileUtils.findWorkspaceFile(fFile);		//SGD Takes a best guess as to what project we were actually in, the specific project information has already been lost above
				if (ws_file != null) {
					fFile = "${workspace_loc}" + ws_file.getFullPath().toOSString();
				}
			}
		}
		
		if (ws_file != null) {
			// Register ourselves as a variable-change listener
			fPathVariableMgr = ws_file.getProject().getPathVariableManager();
			fPathVariableMgr.addChangeListener(this);
		}
	
		// Register ourselves as a listener to the workspace variable manager
		IWorkspaceRoot ws = ResourcesPlugin.getWorkspace().getRoot();
		IPathVariableManager pvm = ws.getPathVariableManager();
		pvm.addChangeListener(this);
		
		fFile = SVFileUtils.normalize(fFile);
		
		fSVDBFile = new SVDBFile(fFile);
		fFSProvider = new SVDBWSFileSystemProvider();
		fFSProvider.init(SVFileUtils.getPathParent(fFile));
	}
	
	@Override
	public void dispose() {
		if (fPathVariableMgr != null) {
			fPathVariableMgr.removeChangeListener(this);
		}
		
		IWorkspaceRoot ws = ResourcesPlugin.getWorkspace().getRoot();
		IPathVariableManager pvm = ws.getPathVariableManager();
		pvm.removeChangeListener(this);
		
		super.dispose();
	}

	public void pathVariableChanged(IPathVariableChangeEvent event) {
		// Any change event triggers a re-build
		updateSVDBFile(getDocumentProvider().getDocument(getEditorInput()));
	}

	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public List<SVDBFilePath> getSVDBFilePath() {
		String project = getProject();
		Tuple<ISVDBIndex, SVDBIndexCollection> result = 
				SVDBIndexUtil.findArgFileIndex(fFile, project);
		
		if (result != null && result.first() != null) {
			return result.first().getFilePath(fFile);
		} else {
			return null;
		}
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
	
	public SVArgFileCodeScanner getCodeScanner() {
		return fCodeScanner;
	}

	@Override
	protected void createActions() {
		super.createActions();
	
		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();

		OpenDeclarationAction od_action = new OpenDeclarationAction(bundle, this);
		od_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".argfile.editor.open.file");
		setAction(SVUiPlugin.PLUGIN_ID + ".svArgFileOpenFile", od_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svArgFileOpenFile", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svArgFileOpenFile", false);
		
		ToggleCommentAction tc_action = new ToggleCommentAction(bundle, "ArgFileToggleComment.", this);
		tc_action.setActionDefinitionId(SVUiPlugin.PLUGIN_ID + ".ArgFileToggleComment");
		tc_action.setEnabled(true);
		tc_action.configure(getSourceViewer(), getSourceViewerConfiguration());
		setAction(SVUiPlugin.PLUGIN_ID + ".svArgFileToggleComment", tc_action);
		markAsStateDependentAction(SVUiPlugin.PLUGIN_ID + ".svArgFileToggleComment", false);
		markAsSelectionDependentAction(SVUiPlugin.PLUGIN_ID + ".svArgFileToggleComment", false);
	}
	
	@Override
	protected void editorContextMenuAboutToShow(IMenuManager menu) {
		super.editorContextMenuAboutToShow(menu);
	
		menu.appendToGroup(ITextEditorActionConstants.GROUP_EDIT,
				getAction(SVUiPlugin.PLUGIN_ID + ".svArgFileOpenFile"));
		/*
		addAction(menu, ITextEditorActionConstants.GROUP_EDIT,
				SVUiPlugin.PLUGIN_ID + ".svArgFileOpenFile");
		 */
	}

	@Override
	protected void initializeKeyBindingScopes() {
		super.initializeKeyBindingScopes();
		setKeyBindingScopes(new String[] {SVUiPlugin.PLUGIN_ID + ".svArgFileEditorContext"});
	}

	
	@Override
	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new SVArgFileSourceViewerConfiguration(this));

		super.createPartControl(parent);
	}
	
	void updateSVDBFile(IDocument doc) {
		if (fUpdateSVDBFileJob == null) {
			synchronized (this) {
				fPendingUpdateSVDBFile = false;
				fUpdateSVDBFileJob = new UpdateSVDBFileJob(doc);
				fUpdateSVDBFileJob.schedule();
			}
		} else {
			fPendingUpdateSVDBFile = true;
		}
		

		/** TODO:
		fLog.debug(LEVEL_MAX, "updateSVDBFile - fIndexMgr=" + fIndexMgr);
	
		if (fIndexMgr != null) {
			if (fUpdateSVDBFileJob == null) {
				synchronized (this) {
					fPendingUpdateSVDBFile = false;
					fUpdateSVDBFileJob = new UpdateSVDBFileJob(doc);
					fUpdateSVDBFileJob.schedule();
				}
			} else {
				fPendingUpdateSVDBFile = true;
			}
		}		
		 */
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
				line = SVDBLocation.unpackLineno(marker.getLocation());
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
				fOutline = new SVArgFileOutlinePage(this);
			}
			return fOutline;
		} else {
			return super.getAdapter(adapter);
		}
	}

	/**
	 * Resolves the path relative to the root file for this
	 * argument file, and the active variable providers
	 * 
	 * @param path
	 * @return
	 */
	public String resolvePath(String path_orig) {
		Tuple<String, ISVArgFileVariableProvider> context = findArgFileContext();

		String path = path_orig;
		String norm_path = null;

		if (fDebugEn) {
			fLog.debug("--> resolvePath: " + path_orig);
		}
		
		// First, expand any variables in the path
		path = SVArgFileUtils.expandVars(path, context.second());

		// relative to the base location or one of the include paths
		if (path.startsWith("..")) {
			if (fDebugEn) {
				fLog.debug("    path starts with ..");
			}
			if ((norm_path = resolveRelativePath(context.first(), path)) == null) {
				/*
				for (String inc_path : fIndexCacheData.getIncludePaths()) {
					if (fDebugEn) {
						fLog.debug("    Check: " + inc_path + " ; " + path);
					}
					if ((norm_path = resolveRelativePath(inc_path, path)) != null) {
						break;
					}
				}
				 */
			} else {
				if (fDebugEn) {
					fLog.debug("norm_path=" + norm_path);
				}
			}
		} else {
			if (path.equals(".")) {
				path = context.first();
			} else if (path.startsWith(".")) {
				path = context.first() + "/" + path.substring(2);
			} else {
				if (!fFSProvider.fileExists(path)) {
					// See if this is an implicit path
					String imp_path = context.first() + "/" + path;

					if (fFSProvider.fileExists(imp_path)) {
						// This path is an implicit relative path that is
						// relative to the base directory
						path = imp_path;
					}
				}
			}
			norm_path = normalizePath(path);
		}
		
		if (norm_path != null && !norm_path.startsWith("${workspace_loc}")) {
			IWorkspaceRoot ws_root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = ws_root.getFileForLocation(new Path(norm_path));
			if (file != null && file.exists()) {
				norm_path = "${workspace_loc}" + file.getFullPath().toOSString();
			}
		}
		
		norm_path = (norm_path != null) ? norm_path : path_orig;
		
		if (fDebugEn) {
			fLog.debug("<-- resolvePath: " + path_orig + " " + norm_path);
		}

		return norm_path;		
	}

	private String resolveRelativePath(
			String		base_location,
			String 		path) {
		String ret = null;
		if (fDebugEn) {
			fLog.debug("--> resolveRelativePath: base=" + base_location + " path=" + path);
		}
		
		// path = getResolvedBaseLocationDir() + "/" + path;
		String norm_path = normalizePath(base_location + "/" + path);

		if (fDebugEn) {
			fLog.debug("    Checking normalizedPath: " + norm_path
					+ " ; ResolvedBaseLocation: " + base_location);
		}

		if (fFSProvider.fileExists(norm_path)) {
			ret = norm_path;
		} else if (base_location.startsWith("${workspace_loc}")) {
			// This could be a reference outside the workspace. Check
			// whether we should reference this as a filesystem path
			// by computing the absolute path
			String base_loc = base_location;
			if (fDebugEn) {
				fLog.debug("Possible outside-workspace path: " + base_loc);
			}
			base_loc = base_loc.substring("${workspace_loc}".length());

			if (fDebugEn) {
				fLog.debug("    base_loc: " + base_loc);
			}

			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IContainer base_dir = null;
			try {
				base_dir = root.getFolder(new Path(base_loc));
			} catch (IllegalArgumentException e) {
			}

			if (base_dir == null) {
				if (base_loc.length() > 0) {
					base_dir = root.getProject(base_loc.substring(1));
				}
			}

			if (fDebugEn) {
				fLog.debug("base_dir=" + ((base_dir != null)?base_dir.getFullPath().toOSString():null));
			}

			if (base_dir != null && base_dir.exists()) {
				IPath base_dir_p = base_dir.getLocation();
				if (base_dir_p != null) {
					if (fDebugEn) {
						fLog.debug("Location of base_dir: " + base_dir_p.toOSString());
					}
					File path_f_t = new File(base_dir_p.toFile(), path);
					if (fDebugEn) {
						fLog.debug("Checking if path exists: " + path_f_t.getAbsolutePath() + " " + path_f_t.exists());
					}
					try {
						if (path_f_t.exists()) {
							if (fDebugEn) {
								fLog.debug("Path does exist outside the project: "
										+ path_f_t.getCanonicalPath());
							}
							norm_path = SVFileUtils.normalize(path_f_t
									.getCanonicalPath());
							ret = norm_path;
						}
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}
		}

		if (fDebugEn) {
			fLog.debug("<-- resolveRelativePath: base=" + base_location + " path=" + path + " ret=" + ret);
		}
		return ret;
	}

	protected static String normalizePath(String path) {
		StringBuilder ret = new StringBuilder();

		int i = path.length() - 1;
		int end;
		int skipCnt = 0;

		// First, skip any trailing '/'
		while (i >= 0 && (path.charAt(i) == '/' || path.charAt(i) == '\\')) {
			i--;
		}

		while (i >= 0) {
			// scan backwards find the next path element
			end = ret.length();

			while (i >= 0 && path.charAt(i) != '/' && path.charAt(i) != '\\') {
				ret.append(path.charAt(i));
				i--;
			}

			if (i != -1) {
				ret.append("/");
				i--;
			}

			if ((ret.length() - end) > 0) {
				String str = ret.substring(end, ret.length() - 1);
				if (str.equals("..")) {
					skipCnt++;
					// remove .. element
					ret.setLength(end);
				} else if (skipCnt > 0) {
					ret.setLength(end);
					skipCnt--;
				}
			}
		}

		return ret.reverse().toString();
	}
	
	private String getProject() {
		String project = null;
		
		if (fFile.startsWith("${workspace_loc}")) {
			String fullpath = fFile.substring("${workspace_loc}".length());
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = root.getFile(new Path(fullpath));
			
			if (file != null) {
				project = file.getProject().getName();
			}
		}
		
		return project;
	}
	
	/**
	 * 
	 * @return <resolved_base_location, variable_provider>
	 */
	public Tuple<String, ISVArgFileVariableProvider> findArgFileContext() {
		// Search for the index to which this file belongs
		String root_file = null;
		String project = getProject();
		
		
		Tuple<ISVDBIndex, SVDBIndexCollection> result = 
				SVDBIndexUtil.findArgFileIndex(fFile, project);
		
		if (result != null) {
			// Located the index to which this arg-file belongs
			ISVDBIndex index = result.first();
			
			SVDBFileTree ft = index.findFileTree(fFile, true);
			
			// Search up to find the root filetree
			
			if (ft != null) {
				// Scan up to the root, stopping if we find a root file
				while (ft.getIncludedByFiles().size() > 0 && !ft.isIncludeRoot()) {
					String ft_path = ft.getIncludedByFiles().get(0);
					SVDBFileTree ft_next = index.findFileTree(ft_path, true);

					if (ft_next == null) {
						break;
					} else {
						ft = ft_next;
					}
				}
			} else {
				System.out.println("Failed to find path " + fFile + " in index " + index.getBaseLocation());
			}
		
			if (ft != null) {
				root_file = ft.getFilePath();
			}
		} else {
			// Failed to find argfile via indexed files.
			// Use this file as the root file
			root_file = fFile;
		}

		String base_location = SVFileUtils.getPathParent(fFile);
		String resolved_base_location = base_location;
		ISVArgFileVariableProvider var_provider = null;
		IProject var_provider_project = null;
	
		if (root_file != null) {
			base_location = SVFileUtils.getPathParent(root_file);
			resolved_base_location = base_location;
			
//			System.out.println("root_file=" + root_file);
			
			if (root_file.startsWith("${workspace_loc}")) {
				IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
				String root_path = root_file.substring("${workspace_loc}".length());
//				System.out.println("root_path=" + root_path);
				IFile root_path_file = root.getFile(new Path(root_path));
				
				if (root_path_file != null) {
					var_provider_project = root_path_file.getProject();
				}
			}
		}

		var_provider = SVCorePlugin.getVariableProvider(var_provider_project);
		
		return new Tuple<String, ISVArgFileVariableProvider>(resolved_base_location, var_provider);
	}


	private class UpdateSVDBFileJob extends Job {
		private IDocument fDocument;
		
		public UpdateSVDBFileJob(IDocument doc) {
			super("Update SVDBFile");
			fDocument = doc;
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			IDocument doc;
			IEditorInput ed_in = getEditorInput();
			if (fDocument != null) {
				doc = fDocument;
			} else {
				doc = getDocumentProvider().getDocument(ed_in);
			}
		
			if (doc == null) {
				try {
					throw new Exception();
				} catch (Exception e) {
					fLog.error("Document NULL during UpdateSVDBFileJob", e);
				}
			}
			
			StringInputStream sin = new StringInputStream(doc.get());
			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();

			Tuple<String, ISVArgFileVariableProvider> context = findArgFileContext();
			SVArgFilePreProcessor pp = new SVArgFilePreProcessor(sin, fFile, 
					context.second());
			SVArgFilePreProcOutput pp_out = pp.preprocess();
			
			SVArgFileParser p = new SVArgFileParser(
					context.first(), // different than resolved base location? // different than resolved base location? // different than resolved base location? // different than resolved base location?
					context.first(),
					fFSProvider);
		
			SVArgFileLexer l = new SVArgFileLexer();
			l.init(null, pp_out);
			
			p.init(l, fFile);

			SVDBFile file = new SVDBFile(fFile);
			try {
				p.parse(file, markers);
			} catch (SVParseException e) {}
			
			addErrorMarkers(markers);
			
			fSVDBFile = file;
			
			if (fOutline != null) {
				fOutline.refresh();
			}
			
			synchronized (SVArgFileEditor.this) {
				fUpdateSVDBFileJob = null;
				if (fPendingUpdateSVDBFile) {
					updateSVDBFile(fDocument);
				}
			}
			
			return Status.OK_STATUS;
		}		
	}
}
