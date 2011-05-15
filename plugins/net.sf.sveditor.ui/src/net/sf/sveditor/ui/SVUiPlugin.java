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


package net.sf.sveditor.ui;

import java.io.IOException;
import java.util.List;
import java.util.MissingResourceException;
import java.util.ResourceBundle;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;

import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.templates.ContextTypeRegistry;
import org.eclipse.jface.text.templates.persistence.TemplateStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.editors.text.templates.ContributionContextTypeRegistry;
import org.eclipse.ui.editors.text.templates.ContributionTemplateStore;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditorPreferenceConstants;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVUiPlugin extends AbstractUIPlugin 
	implements IPropertyChangeListener, ILogListener {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.ui";

	// The shared instance
	private static SVUiPlugin 					fPlugin;
	private ResourceBundle						fResources;
	private WeakHashMap<String, Image>			fImageMap;
	private MessageConsole						fConsole;
	private MessageConsoleStream				fStdoutStream;
	private MessageConsoleStream				fStderrStream;
	private ContributionContextTypeRegistry		fContextRegistry;
	private TemplateStore						fTemplateStore;
	public static final String					CUSTOM_TEMPLATES_KEY = "net.sf.sveditor.customtemplates";
	public static final String					SV_TEMPLATE_CONTEXT = "net.sf.sveditor.ui.svTemplateContext";
	
	// Preference override for testing. Sets the number of spaces a  
	// tab is equivalent to
	private String								fInsertSpaceTestOverride;
	
	private boolean								fStartRefreshJob = false;
	private RefreshIndexJob						fRefreshIndexJob;
	
	
	/**
	 * The constructor
	 */
	public SVUiPlugin() {
		fImageMap = new WeakHashMap<String, Image>();
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
		
		getPreferenceStore().addPropertyChangeListener(this);
		
		boolean debug_en = getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_DEBUG_ENABLED_S);
		SVCorePlugin.getDefault().enableDebug(debug_en);
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
	
	public synchronized void refreshIndex(ISVDBIndex index) {
		if (fRefreshIndexJob == null) {
			fRefreshIndexJob = new RefreshIndexJob(this);
			fRefreshIndexJob.setPriority(Job.LONG);
			fRefreshIndexJob.schedule(1000);
		}
		fRefreshIndexJob.addIndex(index);
	}
	
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

		super.stop(context);
	}
	
	public void propertyChange(PropertyChangeEvent event) {
		if (event.getProperty().equals(SVEditorPrefsConstants.P_DEBUG_ENABLED_S)) {
			SVCorePlugin.getDefault().enableDebug(((Boolean)event.getNewValue()));
		}
	}
	
	public void message(ILogHandle handle, int type, int level, String message) {
		MessageConsoleStream out = null;
		
		if (type == ILogListener.Type_Error) {
			out = getStderrStream();
		} else if (type == ILogListener.Type_Info) {
			out = getStdoutStream();
		} else if (SVCorePlugin.getDefault().getDebugEn()) {
			if ((type & ILogListener.Type_Error) != 0) {
				out = getStderrStream();
			} else {
				out = getStdoutStream();
			}
		}
		
		if (out != null) {
			out.println("[" + handle.getName() + "] " + message);
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
		SVUiPlugin p = getDefault();
		Image ret = null;
		
		if (!p.fImageMap.containsKey(resource)) {
			// Try to load it
			ret = SVUiPlugin.imageDescriptorFromPlugin(
					SVUiPlugin.PLUGIN_ID, resource).createImage();
			p.fImageMap.put(resource, ret);
		}
		
		return p.fImageMap.get(resource);
	}
	
	public MessageConsole getConsole() {
		
		if (fConsole == null) {
			fConsole = new MessageConsole("SVEditor", null);
			ConsolePlugin.getDefault().getConsoleManager().addConsoles(
					new IConsole[] { fConsole });
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
		if (fStdoutStream == null) {
			fStdoutStream = getConsole().newMessageStream();
			fStdoutStream.setActivateOnWrite(true);
			Display.getDefault().syncExec(new Runnable() {
				public void run() {
					fStdoutStream.setColor(
							Display.getDefault().getSystemColor(SWT.COLOR_BLACK));
				}
			});
		}
		return fStdoutStream;
	}

	public MessageConsoleStream getStderrStream() {
		if (fStderrStream == null) {
			fStderrStream = getConsole().newMessageStream();
			fStderrStream.setActivateOnWrite(true);
			Display.getDefault().syncExec(new Runnable() {
				public void run() {
					fStderrStream.setColor(
							Display.getDefault().getSystemColor(SWT.COLOR_RED));
				}
			});
		}
		return fStderrStream;
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
}
