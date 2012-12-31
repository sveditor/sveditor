package net.sf.sveditor.ui.argfile.editor;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.argfile.parser.ISVArgFileVariableProvider;
import net.sf.sveditor.core.argfile.parser.SVArgFileLexer;
import net.sf.sveditor.core.argfile.parser.SVArgFileParser;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcOutput;
import net.sf.sveditor.core.argfile.parser.SVArgFilePreProcessor;
import net.sf.sveditor.core.argfile.parser.SVArgFileUtils;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.argfile.editor.actions.OpenDeclarationAction;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
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

public class SVArgFileEditor extends TextEditor implements ILogLevel {
	private SVArgFileCodeScanner			fCodeScanner;
	private LogHandle						fLog;
	private UpdateSVDBFileJob				fUpdateSVDBFileJob;
	private boolean							fPendingUpdateSVDBFile;
	private String							fFile;
	private SVDBFile						fSVDBFile;
	private SVArgFileOutlinePage			fOutline;
	private ISVDBFileSystemProvider			fFSProvider;
	private boolean							fDebugEn = true;
	
	public SVArgFileEditor() {
		fLog = LogFactory.getLogHandle("SVArgFileEditor");
		fCodeScanner = new SVArgFileCodeScanner();
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
				IFile ws_file = SVFileUtils.findWorkspaceFile(fFile);
				if (ws_file != null) {
					fFile = "${workspace_loc}" + ws_file.getFullPath().toOSString();
				}
			}
		} else if (input instanceof IFileEditorInput) {
			fFile = ((IFileEditorInput)input).getFile().getFullPath().toOSString();
		}
		
		fSVDBFile = new SVDBFile(fFile);
		fFSProvider = new SVDBWSFileSystemProvider();
		fFSProvider.init(SVFileUtils.getPathParent(fFile));
	}
	
	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public void setSelection(ISVDBItemBase it, boolean set_cursor) {
		
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
	
	/**
	 * 
	 * @return <resolved_base_location, variable_provider>
	 */
	private Tuple<String, ISVArgFileVariableProvider> findArgFileContext() {
		// Search for the index to which this file belongs
		String project = null;
		String root_file = null;
		
		if (fFile.startsWith("${workspace_loc}")) {
			String fullpath = fFile.substring("${workspace_loc}".length());
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			
			IFile file = root.getFile(new Path(fullpath));
			
			if (file != null) {
				project = file.getProject().getName();
			}
		}
		
		Tuple<ISVDBIndex, SVDBIndexCollection> result = 
				SVDBIndexUtil.findArgFileIndex(fFile, project);
		
		if (result != null) {
			// Located the index to which this arg-file belongs
			ISVDBIndex index = result.first();
			
			SVDBFileTree ft = index.findFileTree(fFile, true);
			
			// Search up to find the root filetree
			
			if (ft != null) {
				while (ft.getIncludedByFiles().size() > 0) {
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

//		System.out.println("var_provider_project=" + var_provider_project);
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
