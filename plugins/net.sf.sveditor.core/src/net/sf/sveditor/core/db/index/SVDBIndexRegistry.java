package net.sf.sveditor.core.db.index;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.persistence.SVDBDump;
import net.sf.sveditor.core.db.persistence.SVDBLoad;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

/**
 * Central storage for leaf indexes. Provides a central place to locate
 * an index and supports persistence and loading
 * 
 * @author ballance
 *
 */
public class SVDBIndexRegistry implements ISVDBIndexRegistry {
	private Map<String, List<ISVDBIndex>>					fProjectIndexMap;
	private File											fDatabaseDir;
	private Map<String, List<SVDBPersistenceDescriptor>>  	fDatabaseDescMap;

	/**
	 * SVDBIndexRegistry constructor. Only intended to be called by
	 * 
	 * @param state_location
	 */
	public SVDBIndexRegistry() {
		fProjectIndexMap = new WeakHashMap<String, List<ISVDBIndex>>();
		// fDatabaseDir = new File(state_location.toFile(), "db");
		fDatabaseDescMap = new HashMap<String, List<SVDBPersistenceDescriptor>>();
		
	}
	
	public void init(File state_location) {
		fDatabaseDir = new File(state_location, "db");
		fProjectIndexMap.clear();
		fDatabaseDescMap.clear();
		
		load_database_descriptors();
	}
	
	/**
	 * Finds or creates an index
	 * 
	 * @param project        project this index is associated with
	 * @param base_location  base location for the index
	 * @param type           index type
	 * @return
	 */
	public ISVDBIndex findCreateIndex(
			String 					project, 
			String 					base_location, 
			String 					type,
			Map<String, Object>		config) {
		ISVDBIndex ret = null;
		
		System.out.println("findCreateIndex: " + base_location + " ; " + type);
		
		if (!fProjectIndexMap.containsKey(project)) {
			fProjectIndexMap.put(project, new ArrayList<ISVDBIndex>());
		}
		
		List<ISVDBIndex> project_index = fProjectIndexMap.get(project); 
		
		for (ISVDBIndex index : project_index) {
			if (index.getBaseLocation().equals(base_location) &&
					index.getTypeID().equals(type)) {
				ret = index;
				break;
			}
		}
		
		if (ret == null) {
			System.out.println("    Index does not exist -- creating");
			// See about creating a new index
			ISVDBIndexFactory factory = findFactory(type);
			
			System.out.println("factory=" + factory);
			ret = factory.createSVDBIndex(project, base_location, config);
			
			ret.init(this);
			
			project_index.add(ret);
		} else {
			System.out.println("    Index already exists");
		}
		
		return ret;
	}
	
	public void rebuildIndex(String project) {
		if (!fProjectIndexMap.containsKey(project)) {
			return;
		}
		
		for (ISVDBIndex index : fProjectIndexMap.get(project)) {
			if (index.isLoaded()) {
				index.rebuildIndex();
			}
		}
		
		// Also clear any persistence data for the project
		if (fDatabaseDescMap.containsKey(project)) {
			List<SVDBPersistenceDescriptor> db_desc = fDatabaseDescMap.get(project);
			
			for (SVDBPersistenceDescriptor d : db_desc) {
				d.getDBFile().delete();
			}
			fDatabaseDescMap.remove(project);
		}
	}
	
	public boolean loadPersistedData(String project, ISVDBIndex index) {
		System.out.println("loadPersistedData: " + index.getBaseLocation());
		
		String base_location = index.getBaseLocation();
		SVDBPersistenceDescriptor desc = null;
		
		if (!fDatabaseDescMap.containsKey(project)) {
			return false;
		}
		
		List<SVDBPersistenceDescriptor> db_desc = fDatabaseDescMap.get(project);
		
		for (SVDBPersistenceDescriptor d : db_desc) {
			if (d.getBaseLocation().equals(base_location)) {
				desc = d;
				break;
			}
		}
		
		if (desc != null) {
			SVDBLoad loader = new SVDBLoad();
			InputStream in = null;
			boolean loaded = false;
			try {
				in = new FileInputStream(desc.getDBFile());
				System.out.println("Loading from file \"" + desc.getDBFile().getPath() + "\"");
				loader.load(index, in);
				loaded = true;
			} catch (Exception e) {
				e.printStackTrace();
				
				// Remove the DB file, since it's bad... 
				File db_file = desc.getDBFile();
				db_file.delete();
			} finally {
				if (in != null) {
					try {
						in.close();
					} catch (IOException e) {}
				}
			}
			
			return loaded;
		} else {
			return false;
		}
	}
	
	private void load_database_descriptors() {
		if (fDatabaseDir.exists()) {
			SVDBLoad loader = new SVDBLoad();
			
			for (File d : fDatabaseDir.listFiles()) {
				if (d.isDirectory()) {
					String project_name = d.getName();
					List<SVDBPersistenceDescriptor> db_desc = 
						new ArrayList<SVDBPersistenceDescriptor>();
					
					for (File f : d.listFiles()) {
						if (f.isFile() && f.getName().endsWith(".db")) {
							try {
								FileInputStream in = new FileInputStream(f);
								String base = loader.readBaseLocation(in);
								
								System.out.println("base=" + base);
								db_desc.add(
									new SVDBPersistenceDescriptor(f, base));
							} catch (Exception e) {
								e.printStackTrace();
							}
						}
					}
					
					fDatabaseDescMap.put(project_name, db_desc);
				}
			}
		}
	}
	

	/**
	 * Saves the state of loaded indexes to the state_location directory
	 */
	public void save_state() {
		System.out.println("save_state()");
		
		for (String proj_name : fProjectIndexMap.keySet()) {
			save_state(proj_name, fProjectIndexMap.get(proj_name));
		}
		
		// Now, iterate through each saved database and clean up
		// any leftover saved-database files
		
	}
	
	private void save_state(String proj_name, List<ISVDBIndex> index_list) {
		SVDBDump dumper = new SVDBDump();
		List<SVDBPersistenceDescriptor>		db_list = fDatabaseDescMap.get(proj_name);
		
		if (!fDatabaseDir.exists()) {
			if (!fDatabaseDir.mkdirs()) {
				System.out.println("[ERROR] cannot create database dir");
			}
		}
		
		for (ISVDBIndex index : index_list) {
			System.out.println("fDatabaseDir=" + fDatabaseDir + "; proj_name=" + proj_name);
			SVDBFile f = index.findPreProcFile("${workspace_loc}/infact_coverage/sv/inFactCovSv.sv");
			if (f != null) {
				System.out.println("inFactCovSv timestamp: " + f.getLastModified());
			}
			
			if (proj_name == null) {
				System.out.println("proj_name null on : " + index.getClass().getName());
			}
			File proj_db_dir = new File(fDatabaseDir, proj_name);
			
			if (!proj_db_dir.exists()) {
				if (!(proj_db_dir.mkdirs())) {
					System.out.println("[ERROR] cannot create project db dir");
				}
			}
			
			if (index.isLoaded()) {
				// Dump out to the state location
				
				SVDBPersistenceDescriptor d = null;
				
				if (db_list != null) {
					d = findPersistenceDescriptor(db_list, index.getBaseLocation());
				}
				
				File index_file;
				if (d == null) {
					// Pick a new filename
					index_file = pickIndexFileName(proj_db_dir);
				} else {
					index_file = d.getDBFile();
				}
				
				System.out.println("Saving index \"" + index + "\"");
				// Dump the database to disk
				try {
					FileOutputStream out = new FileOutputStream(index_file);
					BufferedOutputStream out_b = new BufferedOutputStream(out);
					
					dumper.dump(index, out_b);
					
					out_b.close();
					out.close();
				} catch (Exception e) {
					e.printStackTrace();
				}
				
				// Delete the index file
				// index_file.delete();
			}
		}
	}
	
	private SVDBPersistenceDescriptor findPersistenceDescriptor(
			List<SVDBPersistenceDescriptor>		db_list,
			String 								base) {
		for (SVDBPersistenceDescriptor d : db_list) {
			if (d.getBaseLocation().equals(base)) {
				return d;
			}
		}
		
		return null;
	}
	
	private static File pickIndexFileName(File db_dir) {
		if (!db_dir.exists()) {
			db_dir.mkdirs();
		}
		
		for (int i=0; i<1000000; i++) {
			File test = new File(db_dir, "index_" + i + ".db");
			
			if (!test.exists()) {
				return test;
			}
		}
		
		return null;
	}
	
	private ISVDBIndexFactory findFactory(String type) {
		ISVDBIndexFactory ret = null;
		IExtensionRegistry rgy = Platform.getExtensionRegistry();
		
		
		IExtensionPoint ext_pt = rgy.getExtensionPoint(
				SVCorePlugin.PLUGIN_ID, "SVDBIndexFactories");
		
		for (IExtension ext_l : ext_pt.getExtensions()) {
			for (IConfigurationElement cel : ext_l.getConfigurationElements()) {
				String id = cel.getAttribute("id");
				
				if (type.equals(id)) {
					try {
						ret = (ISVDBIndexFactory)cel.createExecutableExtension(
							"class");
					} catch (Exception e) {
						e.printStackTrace();
					}
					break;
				}
			}
		}
		
		return ret;
	}
	
	
}
