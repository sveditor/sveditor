package net.sf.sveditor.svt.ui;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.XMLTransformUtils;
import net.sf.sveditor.core.db.project.SVDBPath;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.tagproc.ITemplateParameterProvider;
import net.sf.sveditor.core.tagproc.TemplateParameterProvider;
import net.sf.sveditor.svt.core.SvtCorePlugin;
import net.sf.sveditor.svt.core.templates.IExternalTemplatePathProvider;
import net.sf.sveditor.svt.core.templates.WorkspaceTemplateRegistry;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SvtUiPlugin extends AbstractUIPlugin 
	implements IExternalTemplatePathProvider, IPropertyChangeListener {

	// SV Template Paths
	// Note: copy from SVEditorPrefsConstants
	private static final String TEMPLATE_SETTINGS = "TemplateSettings.";	
	public static final String P_SV_TEMPLATE_PATHS								= TEMPLATE_SETTINGS + "svTemplatePaths";
	public static final String P_SV_TEMPLATE_PROPERTIES							= TEMPLATE_SETTINGS + "svTemplateProperties";

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.svt.ui"; //$NON-NLS-1$

	// The shared instance
	private static SvtUiPlugin plugin;
	
	private List<String>						fTemplatePaths;
	
	private TemplateParameterProvider			fGlobalPrefsProvider;
	
	private WeakHashMap<String, Image>			fImageMap;
	
	/**
	 * The constructor
	 */
	public SvtUiPlugin() {
		fGlobalPrefsProvider = new TemplateParameterProvider();
		fImageMap = new WeakHashMap<String, Image>();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		
		IPreferenceStore pstore = SVUiPlugin.getDefault().getPreferenceStore();

		if (!SVCorePlugin.getTestMode()) {
			pstore.addPropertyChangeListener(this);
		}
		
		WorkspaceTemplateRegistry rgy = SvtCorePlugin.getDefault().getTemplateRgy();
		update_template_paths();
		rgy.addPathProvider(this);
		
		update_global_parameters();		
	}

	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}
	
	public void propertyChange(PropertyChangeEvent event) {
		
		if (event.getProperty().equals(P_SV_TEMPLATE_PATHS)) {
			// propagate to template registry
			update_template_paths();
		} else if (event.getProperty().equals(P_SV_TEMPLATE_PROPERTIES)) {
			update_global_parameters();
		}
	}

	private void update_template_paths() {
		IPreferenceStore pstore = SVUiPlugin.getDefault().getPreferenceStore();
		fTemplatePaths = parse_paths(pstore.getString(P_SV_TEMPLATE_PATHS));
		
		// Add in any project-specific template paths
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		for (IProject p : root.getProjects()) {
			if (!p.isAccessible() || !p.isOpen()) {
				continue;
			}
			SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
			SVDBProjectData pdata = pmgr.getProjectData(p);

			for (SVDBPath tpath : pdata.getProjectFileWrapper().getTemplatePaths()) {
				String path = tpath.getPath();
			
				// Expand any variables
				path = SVFileUtils.expandVars(path, p.getName(), true);
				
				if (!fTemplatePaths.contains(path)) {
					fTemplatePaths.add(path);
				}
			}
		}
	}
	
	private static List<String> parse_paths(String stringList) {
		
		StringTokenizer st = new StringTokenizer(stringList, File.pathSeparator
				+ "\n\r");//$NON-NLS-1$
		ArrayList<String> v = new ArrayList<String>();
		while (st.hasMoreElements()) {
			v.add((String)st.nextElement());
		}
		return v;
	}
	
	private void update_global_parameters() {
		Map<String, String> params = null;
		IPreferenceStore pstore = SVUiPlugin.getDefault().getPreferenceStore();
		
		try {
			params = XMLTransformUtils.xml2Map(pstore.getString(P_SV_TEMPLATE_PROPERTIES),
				"parameters", "parameter");
		} catch (Exception e) {}
		
		if (params != null) {
			fGlobalPrefsProvider = new TemplateParameterProvider(params);
		}
	}	

	public List<String> getExternalTemplatePath() {
		return fTemplatePaths;
	}
	
	public ITemplateParameterProvider getGlobalTemplateParameters() {
		return fGlobalPrefsProvider;
	}
	
	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static SvtUiPlugin getDefault() {
		return plugin;
	}

	public static Image getImage(String resource) {
		SvtUiPlugin p = getDefault();
		Image ret = null;
		
		if (!p.fImageMap.containsKey(resource)) {
			// Try to load it
			ret = imageDescriptorFromPlugin(PLUGIN_ID, resource).createImage();
			p.fImageMap.put(resource, ret);
		}
		
		return p.fImageMap.get(resource);
	}	
}
