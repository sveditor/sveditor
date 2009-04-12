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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileMerger;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemPrint;
import net.sf.sveditor.core.db.persistence.SVDBDump;
import net.sf.sveditor.core.db.persistence.SVDBLoad;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;

/**
 * Central storage for leaf indexes. Provides a central place to locate
 * an index and supports persistence and loading
 * 
 * @author ballance
 *
 */
public class SVDBIndexRegistry implements ISVDBIndexRegistry {
	private List<ISVDBIndex>					fIndexList;
	private File								fDatabaseDir;
	private List<SVDBPersistenceDescriptor>		fDatabaseDescriptors;

	/**
	 * SVDBIndexRegistry constructor. Only intended to be called by
	 * 
	 * @param state_location
	 */
	public SVDBIndexRegistry(IPath state_location) {
		
		fIndexList   = new ArrayList<ISVDBIndex>();
		fDatabaseDir = new File(state_location.toFile(), "db");
		fDatabaseDescriptors = new ArrayList<SVDBPersistenceDescriptor>();
		
		load_database_descriptors();
	}
	
	public ISVDBIndex findCreateIndex(String base_location, String type) {
		ISVDBIndex ret = null;
		
		System.out.println("findCreateIndex: " +base_location + " ; " + type);
		
		for (ISVDBIndex index : fIndexList) {
			if (index.getBaseLocation().getPath().equals(base_location) &&
					index.getTypeID().equals(type)) {
				ret = index;
				break;
			}
		}
		
		if (ret == null) {
			// See about creating a new index
			ISVDBIndexFactory factory = findFactory(type);
			
			System.out.println("factory=" + factory);
			ret = factory.createSVDBIndex(base_location);
			
			ret.init(this);
			
			fIndexList.add(ret);
		}
		
		return ret;
	}
	
	public boolean loadPersistedData(ISVDBIndex index) {
		System.out.println("loadPersistedData: " + index.getBaseLocation().getPath());
		
		// Persistence disabled for now
		if (true) {
			return false;
		}
		String base_location = index.getBaseLocation().getPath();
		SVDBPersistenceDescriptor desc = null;
		
		for (SVDBPersistenceDescriptor d : fDatabaseDescriptors) {
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
			
			for (File f : fDatabaseDir.listFiles()) {
				if (f.isFile() && f.getName().endsWith(".db")) {
					try {
						FileInputStream in = new FileInputStream(f);
						String base = loader.readBaseLocation(in);
						
						System.out.println("base=" + base);
						fDatabaseDescriptors.add(
							new SVDBPersistenceDescriptor(f, base));
					} catch (Exception e) {
						e.printStackTrace();
					}
				}
			}
		}
	}
	

	/**
	 * Saves the state of loaded indexes to the state_location directory
	 */
	public void save_state() {
		SVDBDump dumper = new SVDBDump();
		System.out.println("save_state()");
		
		for (ISVDBIndex index : fIndexList) {
			if (index.isLoaded()) {
				// Dump out to the state location
				
				if (!fDatabaseDir.exists()) {
					if (!fDatabaseDir.mkdirs()) {
						System.out.println("[ERROR] cannot create database dir");
					}
				}
				
				SVDBPersistenceDescriptor d = findPersistenceDescriptor(
						index.getBaseLocation().getPath());
				
				File index_file;
				if (d == null) {
					// Pick a new filename
					index_file = pickIndexFileName();
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
				
				// Okay, now let's load back the files to check
				SVDBLoad loader = new SVDBLoad();
				try {
					FileInputStream in = new FileInputStream(index_file);
					Map<File, SVDBFile> pp_map = new HashMap<File, SVDBFile>();
					Map<File, SVDBFile> db_map = new HashMap<File, SVDBFile>();
					
					loader.load(pp_map, db_map, in);
					
					// Now, compare
					
					SVDBFile pp_file = pp_map.get(new File(
							"plugin:/net.sf.sveditor.libs.ovm/ovm-2.0.1/src/macros/ovm_object_defines.svh"));
					
					if (pp_file != null) {
						SVDBFile pp_file_orig = index.getPreProcFileMap().get(new File(
								"plugin:/net.sf.sveditor.libs.ovm/ovm-2.0.1/src/macros/ovm_object_defines.svh"));
						
						System.out.println("Original file: ");
						SVDBItemPrint.printItem(pp_file_orig);
						
						System.out.println("Loaded file: ");
						SVDBItemPrint.printItem(pp_file);
					}
					
					List<SVDBItem> adds = new ArrayList<SVDBItem>();
					List<SVDBItem> rems = new ArrayList<SVDBItem>();
					List<SVDBItem> chgs = new ArrayList<SVDBItem>();
					
					for (File f : index.getPreProcFileMap().keySet()) {
						SVDBFile orig_file = index.getPreProcFileMap().get(f);
						SVDBFile load_file = pp_map.get(f);
						
						adds.clear();
						rems.clear();
						chgs.clear();
						
						SVDBFileMerger.merge(orig_file, load_file, 
								adds, rems, chgs);
						
						if (adds.size() > 0) {
							System.out.println("" + adds.size() + " adds in pp file \"" + 
									f.getPath() + "\"");
						}
						if (rems.size() > 0) {
							System.out.println("" + rems.size() + " rems in pp file \"" + 
									f.getPath() + "\"");
						}
						if (chgs.size() > 0) {
							System.out.println("" + chgs.size() + " chgs in pp file \"" + 
									f.getPath() + "\"");
						}
					}
					
					for (File f : index.getFileDB().keySet()) {
						SVDBFile orig_file = index.getFileDB().get(f);
						SVDBFile load_file = db_map.get(f);
						
						adds.clear();
						rems.clear();
						chgs.clear();
						
						SVDBFileMerger.merge(orig_file, load_file, 
								adds, rems, chgs);
						
						if (adds.size() > 0) {
							System.out.println("" + adds.size() + " adds in db file \"" + 
									f.getPath() + "\"");
						}
						if (rems.size() > 0) {
							System.out.println("" + rems.size() + " rems in db file \"" + 
									f.getPath() + "\"");
						}
						if (chgs.size() > 0) {
							System.out.println("" + chgs.size() + " chgs in db file \"" + 
									f.getPath() + "\"");
						}
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
				
				// Delete the index file
				// index_file.delete();
				
			}
		}
		
		// Now, iterate through each saved database and clean up
		// any leftover saved-database files
		
	}
	
	private SVDBPersistenceDescriptor findPersistenceDescriptor(String base) {
		for (SVDBPersistenceDescriptor d : fDatabaseDescriptors) {
			if (d.getBaseLocation().equals(base)) {
				return d;
			}
		}
		
		return null;
	}
	
	private File pickIndexFileName() {
		if (!fDatabaseDir.exists()) {
			fDatabaseDir.mkdirs();
		}
		
		for (int i=0; i<1000000; i++) {
			File test = new File(fDatabaseDir, "index_" + i + ".db");
			
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
