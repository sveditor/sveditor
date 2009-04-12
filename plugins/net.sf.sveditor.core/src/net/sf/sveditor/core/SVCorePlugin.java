package net.sf.sveditor.core;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexList;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBPluginLibDescriptor;
import net.sf.sveditor.core.db.project.SVDBProjectManager;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class SVCorePlugin extends Plugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sf.sveditor.core";

	// The shared instance
	private static SVCorePlugin 			fPlugin;
	private SVDBWorkspaceFileManager		fSVDBMgr;
	private SVTodoScanner					fTodoScanner;
	private SVDBProjectManager				fProjManager;
	private SVDBIndexList					fBuiltinList;	
	private SVDBIndexRegistry				fIndexRegistry;
	
	/**
	 * The constructor
	 */
	public SVCorePlugin() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		fPlugin = this;
		fTodoScanner = new SVTodoScanner();
		
		loadBuiltInLibraries();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		fPlugin = null;
		
		if (fSVDBMgr != null) {
			fSVDBMgr.dispose();
			fSVDBMgr = null;
		}
		
		if (fTodoScanner != null) {
			fTodoScanner.dispose();
		}
		
		if (fProjManager != null) {
			fProjManager.dispose();
		}
		
		if (fIndexRegistry != null) {
			fIndexRegistry.save_state();
		}
		
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static SVCorePlugin getDefault() {
		return fPlugin;
	}
	
	public SVDBProjectManager getProjMgr() {
		if (fProjManager == null) {
			fProjManager = new SVDBProjectManager();
		}
		return fProjManager;
	}
	
	public SVDBWorkspaceFileManager getSVDBMgr() {
		if (fSVDBMgr == null) {
			fSVDBMgr = new SVDBWorkspaceFileManager();
		}
		return fSVDBMgr;
	}
	
	public List<SVDBPluginLibDescriptor> getPluginLibList() {
		List<SVDBPluginLibDescriptor> ret = new ArrayList<SVDBPluginLibDescriptor>();

		IExtensionRegistry rgy = Platform.getExtensionRegistry();
		IExtensionPoint pt = rgy.getExtensionPoint(PLUGIN_ID, "SVLibraries");
		
		for (IExtension ext : pt.getExtensions()) {
			for (IConfigurationElement cel : ext.getConfigurationElements()) {
				String name       = cel.getAttribute("name");
				String path       = cel.getAttribute("path");
				String id         = cel.getAttribute("id");
				String is_dflt_s  = cel.getAttribute("default");
				String desc       = "";
				
				boolean is_default = (is_dflt_s != null && is_dflt_s.equals("true"));
				
				for (IConfigurationElement cel_i : cel.getChildren()) {
					if (cel_i.getName().equals("description")) {
						desc = cel_i.getValue();
					}
				}
				
				SVDBPluginLibDescriptor lib_desc = new SVDBPluginLibDescriptor(
						name, id, ext.getNamespaceIdentifier(), path,
						is_default, desc);
				
				ret.add(lib_desc);

			}
		}
		
		super.getStateLocation();

		return ret;
	}
	
	public SVDBIndexRegistry getSVDBIndexRegistry() {
		if (fIndexRegistry == null) {
			fIndexRegistry = new SVDBIndexRegistry(getStateLocation());
		}
		
		return fIndexRegistry;
	}
	
	private void loadBuiltInLibraries() {
		fBuiltinList = new SVDBIndexList(new File("BUILTIN"));
		
		SVDBIndexRegistry index_rgy = getSVDBIndexRegistry();
		
		
		for (SVDBPluginLibDescriptor lib_desc : getPluginLibList()) {
			ISVDBIndex index = index_rgy.findCreateIndex(
					"plugin:/" + lib_desc.getNamespace() + "/" + lib_desc.getPath(), 
					ISVDBIndexFactory.TYPE_PluginLibIndex);
			
			fBuiltinList.addIndex(index);
		}

		/*
		File index_dir = new File("/tmp/index_dir");
		
		if (!index_dir.isDirectory()) {
			index_dir.mkdirs();
		}
		
		for (SVDBPluginLibDescriptor lib_desc : getPluginLibList()) {
			SVDBPluginLibIndex index = new SVDBPluginLibIndex(
					lib_desc.getName(), lib_desc.getNamespace(),
					lib_desc.getPath());
			
			try {
				SVDBDump dumper = new SVDBDump();
				
				OutputStream out = new FileOutputStream(
						new File(index_dir, index.toString() + ".db"));
				BufferedOutputStream out_b = new BufferedOutputStream(out);
				
				
				long start = System.currentTimeMillis();
				index.getPreProcFileMap();
				index.getFileDB();
				long end = System.currentTimeMillis();
				
				start = System.currentTimeMillis();
				dumper.dump(index, out_b);
				end = System.currentTimeMillis();
				
				System.out.println("dump " + lib_desc.getName() + " in " + 
						(end-start));
				
				out_b.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
			
			try {
				SVDBLoad load = new SVDBLoad();
				
				InputStream in = new FileInputStream(
						new File(index_dir, index.toString() + ".db"));
				
				long start = System.currentTimeMillis();
				load.load(index, in);
				long end = System.currentTimeMillis();
				
				System.out.println("load " + lib_desc.getName() + " in " +
						(end-start));
				
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
			}
			
			fBuiltinList.addIndex(index);
		}
		 */
	}
	
	public ISVDBIndex getBuiltinIndex() {
		if (fBuiltinList == null) {
			loadBuiltInLibraries();
		}
		return fBuiltinList;
	}
}


