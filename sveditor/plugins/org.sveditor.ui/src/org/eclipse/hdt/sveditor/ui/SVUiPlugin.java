/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.MissingResourceException;
import java.util.ResourceBundle;
import java.util.WeakHashMap;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.hdt.sveditor.core.ILineListener;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.XMLTransformUtils;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.ILogListener;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.parser.SVParserConfig;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.templates.ContextTypeRegistry;
import org.eclipse.jface.text.templates.persistence.TemplateStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.editors.text.templates.ContributionContextTypeRegistry;
import org.eclipse.ui.editors.text.templates.ContributionTemplateStore;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditorPreferenceConstants;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.osgi.framework.BundleContext;
import org.osgi.framework.Version;

import org.eclipse.hdt.sveditor.ui.console.SVEMessageConsole;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.pref.SVEditorPrefsConstants;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVUiPlugin extends AbstractUIPlugin 
	implements IPropertyChangeListener, ILogListener {
	
	private class LogMessage {
		ILogHandle				handle;
		int						type;
		int						level;
		String					message;
	}

	// The plug-in ID
	public static final String PLUGIN_ID = "org.eclipse.hdt.sveditor.ui";

	// The shared instance
	private static SVUiPlugin 					fPlugin;
	private ResourceBundle						fResources;
	private WeakHashMap<String, Image>			fImageMap;
	private SVEMessageConsole							fConsole;
	private ContributionContextTypeRegistry		fContextRegistry;
	private TemplateStore						fTemplateStore;
	private boolean								fDebugConsole;
	public static final String					CUSTOM_TEMPLATES_KEY = "org.eclipse.hdt.sveditor.customtemplates";
	public static final String					SV_TEMPLATE_CONTEXT = "org.eclipse.hdt.sveditor.ui.svTemplateContext";
	
	// Preference override for testing. Sets the number of spaces a  
	// tab is equivalent to
	private String								fInsertSpaceTestOverride;
	
	private boolean								fStartRefreshJob = false;
	private RefreshIndexJob						fRefreshIndexJob;
	
	private List<LogMessage>					fLogMessageQueue;
	private boolean								fLogMessageScheduled;
	
	private SVBuildConsoleListener				fBuilderOutputListener;
	private SVBuildProcessListener				fBuildProcessListener;
	
	/**
	 * Small change 1
	 */
	
	/**
	 * The constructor
	 */
	public SVUiPlugin() {
		fImageMap = new WeakHashMap<String, Image>();
		fLogMessageQueue = new ArrayList<SVUiPlugin.LogMessage>();
		
		fBuilderOutputListener = new SVBuildConsoleListener();
		fBuildProcessListener = new SVBuildProcessListener();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		fPlugin = this;
		
		// add console listener
		LogFactory.getDefault().addLogListener(this);
		
		SVCorePlugin.getDefault().addStdoutLineListener(fStdoutLineListener);
		SVCorePlugin.getDefault().addStderrLineListener(fStderrLineListener);
		SVCorePlugin.getDefault().setBuilderOutputListener(fBuilderOutputListener);
		SVCorePlugin.getDefault().setBuildProcessListener(fBuildProcessListener);
		
		// Don't change settings if we're in test mode
		if (!SVCorePlugin.getTestMode()) {
			getPreferenceStore().addPropertyChangeListener(this);
			SVCorePlugin.getDefault().setDebugLevel(getDebugLevel(
					getPreferenceStore().getString(SVEditorPrefsConstants.P_DEBUG_LEVEL_S)));
			SVCorePlugin.getDefault().setFileExtLanguageLevelOverride(
					getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OVERRIDE_FILE_EXTENSION_LANGUAGE_LEVEL));
			update_parser_prefs();
		}
	}
	
	/**
	 * Get the Eclipse platform version.
	 * @return
	 */
	public static Version getPlatformVersion() {
		return Platform.getBundle("org.eclipse.platform").getVersion();
	}

	/**
	 * Determines whether calls to org.eclipse.jface.text.FindReplaceDocumentAdapter.find should escape any
	 * regular expression characters in the search string when performing a word search. The behaviour has
	 * changed with Eclipse 4.3.0 such that the search string is now correctly escaped in the find method
	 * (Eclipse bug #386751; commit: a68f0663)
	 *
	 * @return true if the string should be escaped with Pattern.quote().
	 */
	public static boolean shouldEscapeFindWordPattern() {
		return (getPlatformVersion().compareTo(new Version(4,3,0)) < 0);
	}


	public static IWorkbenchPage getActivePage() {
		return null;
//		return getDefault().getActivePage() ;
	}
	
	public static Shell getActiveWorkbenchShell() {
		return getDefault().getWorkbench().getActiveWorkbenchWindow().getShell();
	}
	
	public static SVEditor getActiveSVEditor() {
		IWorkbenchWindow w = getDefault().getWorkbench().getActiveWorkbenchWindow();
		IEditorPart p = w.getActivePage().getActiveEditor();
		
		if (p != null && p instanceof SVEditor) {
			return (SVEditor)p;
		} else {
			return null;
		}
	}
	
//	public void buildProcess(Process p) {
//		ILaunchConfigurationType lct = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurationType(
//				PLUGIN_ID + ".indexBuildLaunchConfiguration");
//		ILaunchConfigurationWorkingCopy lc = null;
//		
//		try {
//			lc = lct.newInstance(null, "Foo");
//		} catch (CoreException e) {
//			e.printStackTrace();
//		}
//		Map<String, Object> lc_attr = new HashMap<String, Object>();
//		lc_attr.put("PROCESS", p);
//		lc.setAttributes(lc_attr);
//		System.out.println("--> launch");
//		final ILaunchConfigurationWorkingCopy lc_f = lc;
//		Display.getDefault().asyncExec(new Runnable() {
//			@Override
//			public void run() {
//				try {
//					lc_f.launch("run", new NullProgressMonitor());
//				} catch (CoreException e) {
//					e.printStackTrace();
//				}
//			}
//		});
//		// Execute any events
////		while (Display.getDefault().readAndDispatch()) { }
//		System.out.println("<-- launch");
//		
//	}
	
	

	public static void log(Exception e) {
		e.printStackTrace();
	}
	
	public static void log(IStatus e) {
	}
	
	private void update_parser_prefs() {
		try {
			Map<String, String> parser_opts = XMLTransformUtils.xml2Map(
					getPreferenceStore().getString(SVEditorPrefsConstants.P_SV_CODE_STYLE_PREFS),
					"preferences", "preference");
		
			SVParserConfig cfg = SVCorePlugin.getDefault().getParserConfig();
			for (Entry<String, String> entry : parser_opts.entrySet()) {
				cfg.setOption(entry.getKey(), entry.getValue().equals("true"));
			}
		} catch (Exception e) {}
		
	}
	


	
	private int getDebugLevel(String level_s) {
		if (level_s.equals("LEVEL_MIN")) {
			return ILogLevel.LEVEL_MIN;
		} else if (level_s.equals("LEVEL_MID")) {
			return ILogLevel.LEVEL_MID;
		} else if (level_s.equals("LEVEL_MAX")) {
			return ILogLevel.LEVEL_MAX;
		} else {
			return ILogLevel.LEVEL_OFF;
		}
	}
	
	// Called by SVEditor on startup
	public synchronized void startRefreshJob() {
		if (!fStartRefreshJob) {
			RefreshProjectIndexesJob rj = new RefreshProjectIndexesJob();
			rj.setPriority(Job.LONG);
			rj.schedule(5000);
			
			fStartRefreshJob = true;
		}
	}
	
	/*
	public synchronized void refreshIndex(ISVDBIndex index) {
		if (fRefreshIndexJob == null) {
			fRefreshIndexJob = new RefreshIndexJob(this);
			fRefreshIndexJob.setPriority(Job.LONG);
			fRefreshIndexJob.schedule(1000);
		}
		fRefreshIndexJob.addIndex(index);
	}
	 */
	
	public synchronized void refreshIndexList(List<ISVDBIndex> list) {
		if (fRefreshIndexJob == null) {
			fRefreshIndexJob = new RefreshIndexJob(this);
			fRefreshIndexJob.setPriority(Job.LONG);
			fRefreshIndexJob.schedule(1000);
		}
		fRefreshIndexJob.addIndexList(list);
	}
	
	public synchronized void refreshJobComplete() {
		fRefreshIndexJob = null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		fPlugin = null;
		
		getPreferenceStore().removePropertyChangeListener(this);

		LogFactory.getDefault().removeLogListener(this);
		
		SVCorePlugin.getDefault().removeStdoutLineListener(fStdoutLineListener);
		SVCorePlugin.getDefault().removeStderrLineListener(fStderrLineListener);

		super.stop(context);
	}
	
	public void propertyChange(PropertyChangeEvent event) {
		if (event.getProperty().equals(SVEditorPrefsConstants.P_DEBUG_LEVEL_S)) {
			SVCorePlugin.getDefault().setDebugLevel(getDebugLevel((String)event.getNewValue()));
		} else if (event.getProperty().equals(SVEditorPrefsConstants.P_DEBUG_CONSOLE_S)) {
			synchronized (fLogMessageQueue) {
				fDebugConsole = (Boolean)event.getNewValue();
			}
		} else if (event.getProperty().equals(SVEditorPrefsConstants.P_SV_CODE_STYLE_PREFS)) {
			update_parser_prefs();
		} else if (event.getProperty().equals(SVEditorPrefsConstants.P_OVERRIDE_FILE_EXTENSION_LANGUAGE_LEVEL)) {
			SVCorePlugin.getDefault().setFileExtLanguageLevelOverride(event.getNewValue().equals("true"));
		}

	}
	
	
	private Runnable logMessageRunnable = new Runnable() {
		public void run() {
			synchronized (fLogMessageQueue) {
				for (LogMessage msg : fLogMessageQueue) {
					ILogHandle handle = msg.handle;
					String handle_tag = (handle != null)?("[" + handle.getName() + "] "):"";
					int type = msg.type;
					int level = msg.level;
					String message = msg.message;
					MessageConsoleStream out = null;

					if (type == ILogListener.Type_Error) {
						out = getStderrStream();
					} else if (type == ILogListener.Type_Info) {
						out = getStdoutStream();
					} else if (SVCorePlugin.getDefault().getDebugLevel() >= level) {
						if ((type & ILogListener.Type_Error) != 0) {
							out = getStderrStream();
						} else {
							out = getStdoutStream();
						}
					}

					if (out != null) {
						out.println(handle_tag + message);
					}
				}
				fLogMessageQueue.clear();
				fLogMessageScheduled = false;
			}
		}
	};
	
	private ILineListener fStderrLineListener = new ILineListener() {
		public void line(String l) {
			MessageConsoleStream err = getStderrStream();
			err.println(l);
		}
	};
	
	private ILineListener fStdoutLineListener = new ILineListener() {
		public void line(String l) {
			MessageConsoleStream out = getStdoutStream();
			out.println(l);
		}
	};
	
	public void message(ILogHandle handle, int type, int level, String message) {
		synchronized (fLogMessageQueue) {
			if (!fDebugConsole && 
					type != ILogListener.Type_Error &&
					type != ILogListener.Type_Info) {
				// No output to console
				return;
			}
			LogMessage msg = new LogMessage();
			msg.handle = handle;
			msg.type = type;
			msg.level = level;
			msg.message = message;
			
			fLogMessageQueue.add(msg);
			
			if (!fLogMessageScheduled) {
				Display.getDefault().asyncExec(logMessageRunnable);
				fLogMessageScheduled = true;
			}
		}

	}
	
	public ResourceBundle getResources() {
		if (fResources == null) {
			try {
				fResources = ResourceBundle.getBundle(PLUGIN_ID + ".SVUIResources");
			} catch (MissingResourceException e) {
				e.printStackTrace();
			}
		}
		return fResources;
	}
	
	
	public static Image getImage(String resource) {
		return getImage(SVUiPlugin.PLUGIN_ID, resource);
	}
	
	public static Image getImage(String bundle, String resource) {
		SVUiPlugin p = getDefault();
		Image ret = null;
		
		if (!p.fImageMap.containsKey(resource)) {
			// Try to load it
			ret = SVUiPlugin.imageDescriptorFromPlugin(
					bundle, resource).createImage();
			p.fImageMap.put(resource, ret);
		}
		
		return p.fImageMap.get(resource);
		
	}

	public static ImageDescriptor getImageDescriptor(String resource) {
		return SVUiPlugin.imageDescriptorFromPlugin(
				SVUiPlugin.PLUGIN_ID, resource);
	}

	public SVEMessageConsole getConsole() {
		
		if (fConsole == null) {
			fConsole = SVEMessageConsole.getConsole("SVEditor");
		}
		
		return fConsole;
	}
	
	
	public ContextTypeRegistry getContextTypeRegistry() {
		if (fContextRegistry == null) {
			fContextRegistry = new ContributionContextTypeRegistry();
			fContextRegistry.addContextType(SV_TEMPLATE_CONTEXT);
		}
		return fContextRegistry;
	}
	
	public TemplateStore getTemplateStore() {
		if (fTemplateStore == null) {
			fTemplateStore = new ContributionTemplateStore(
					SVUiPlugin.getDefault().getContextTypeRegistry(), 
					SVUiPlugin.getDefault().getPreferenceStore(), 
					SVUiPlugin.CUSTOM_TEMPLATES_KEY);
			try {
				fTemplateStore.load();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		return fTemplateStore;
	}
	
	public MessageConsoleStream getStdoutStream() {
		return getConsole().getStdout();
	}

	public MessageConsoleStream getStderrStream() {
		return getConsole().getStderr();
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static SVUiPlugin getDefault() {
		return fPlugin;
	}
	
	/**
	 * Return the named preferences section 
	 * 
	 * @param name
	 * @return
	 */
	public IDialogSettings getDialogSettingsSection(String name) {
		IDialogSettings dialogSettings= getDialogSettings();
		IDialogSettings section= dialogSettings.getSection(name);
		if (section == null) {
			section= dialogSettings.addNewSection(name);
		}
		return section;
	}
	
	/** 
	 * Get the chained preferences store from this plug-in and the Editor plug-in
	 * 
	 * @return
	 */
	public IPreferenceStore getChainedPrefs() {
		ChainedPreferenceStore ret = new ChainedPreferenceStore(
				new IPreferenceStore[] {
						getPreferenceStore(),
						EditorsUI.getPreferenceStore()
				});
		return ret;
	}
	
	/**
	 * Get the indent increment from the user's preferences
	 * 
	 * @return
	 */
	public String getIndentIncr() {
		IPreferenceStore chainedPrefs = SVUiPlugin.getDefault().getChainedPrefs();
		boolean spaces_for_tabs = chainedPrefs.getBoolean(
				AbstractDecoratedTextEditorPreferenceConstants.EDITOR_SPACES_FOR_TABS);
		int tab_width = chainedPrefs.getInt(
				AbstractDecoratedTextEditorPreferenceConstants.EDITOR_TAB_WIDTH);
		
		if (fInsertSpaceTestOverride != null) {
			return fInsertSpaceTestOverride;
		} else {
			if (spaces_for_tabs) {
				String ret = "";
				for (int i=0; i<tab_width; i++) {
					ret += " ";
				}
				return ret;
			} else {
				return "\t";
			}
		}
	}
	
	public int getTabWidth() {
		IPreferenceStore chainedPrefs = SVUiPlugin.getDefault().getChainedPrefs();
		int tab_width = chainedPrefs.getInt(
				AbstractDecoratedTextEditorPreferenceConstants.EDITOR_TAB_WIDTH);
		return tab_width;
	}
	
	public boolean getBooleanPref(String id) {
		IPreferenceStore chainedPrefs = SVUiPlugin.getDefault().getChainedPrefs();
		boolean val = chainedPrefs.getBoolean(id);

		return val;
	}
	
	public int getIntegerPref(String id) {
		IPreferenceStore chainedPrefs = SVUiPlugin.getDefault().getChainedPrefs();
		int val = chainedPrefs.getInt(id);

		return val;
	}
	
}
