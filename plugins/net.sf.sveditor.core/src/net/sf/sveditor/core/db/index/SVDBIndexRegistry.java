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


package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.persistence.SVDBDump;
import net.sf.sveditor.core.db.persistence.SVDBLoad;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

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
	public static final String								GLOBAL_PROJECT = "GLOBAL";
	
	private SVDBIndexCollectionMgr							fGlobalIndexMgr;
	private Map<String, List<ISVDBIndex>>					fProjectIndexMap;
	private File											fDatabaseDir;
	private Map<String, List<SVDBPersistenceDescriptor>>  	fDatabaseDescMap;
	private LogHandle										fLog;

	/**
	 * SVDBIndexRegistry constructor. Only intended to be called by
	 * 
	 * @param state_location
	 */
	public SVDBIndexRegistry() {
		fProjectIndexMap = new WeakHashMap<String, List<ISVDBIndex>>();
		fDatabaseDescMap = new HashMap<String, List<SVDBPersistenceDescriptor>>();
		fLog = LogFactory.getLogHandle("SVDBIndexRegistry");
		fGlobalIndexMgr = getGlobalIndexMgr();
	}
	
	public void init(File state_location) {
		fProjectIndexMap.clear();
		fDatabaseDescMap.clear();
		if (state_location != null) {
			fDatabaseDir = new File(state_location, "db");
			load_database_descriptors();
		} else {
			fDatabaseDir = null;
		}
		fGlobalIndexMgr = getGlobalIndexMgr();
	}
	
	public List<ISVDBIndex> getProjectIndexList(String project) {
		if (fProjectIndexMap.containsKey(project)) {
			return fProjectIndexMap.get(project);
		} else {
			return new ArrayList<ISVDBIndex>();
		}
	}
	
	public SVDBIndexCollectionMgr getGlobalIndexMgr() {
		if (fGlobalIndexMgr == null) {
			fGlobalIndexMgr = new SVDBIndexCollectionMgr(GLOBAL_PROJECT);
			
			// Ensure the global index has access to the built-in types
			ISVDBIndex index = findCreateIndex(
					SVDBIndexRegistry.GLOBAL_PROJECT, 
					SVCorePlugin.SV_BUILTIN_LIBRARY, 
					SVDBPluginLibIndexFactory.TYPE, null);
			if (index != null) {
				fGlobalIndexMgr.addPluginLibrary(index);
			}
		}
		return fGlobalIndexMgr;
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
		
		fLog.debug("findCreateIndex: " + base_location + " ; " + type);
		
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
			fLog.debug("    Index does not exist -- creating");
			// See about creating a new index
			ISVDBIndexFactory factory = findFactory(type);
			
			ret = factory.createSVDBIndex(project, base_location, config);
			
			ret.init(this);
			
			project_index.add(ret);
		} else {
			fLog.debug("    Index already exists");
		}
		
		return ret;
	}
	
	public void rebuildIndex(String project) {
		fLog.debug("rebuildIndex \"" + project + "\"");
		if (!fProjectIndexMap.containsKey(project)) {
			fLog.debug("    skipping - not a registered project");
			return;
		}
		
		for (ISVDBIndex index : fProjectIndexMap.get(project)) {
			if (index.isLoaded()) {
				fLog.debug("    rebuild index \"" + index.getBaseLocation() + "\"");
				index.rebuildIndex();
			} else {
				fLog.debug("    skipping index \"" + index.getBaseLocation() + "\" - not loaded");
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
		fLog.debug("loadPersistedData: " + index.getBaseLocation() + "(project=" + project + ")");
		
		String base_location = index.getBaseLocation();
		SVDBPersistenceDescriptor desc = null;
		
		if (!fDatabaseDescMap.containsKey(project)) {
			fLog.debug("    Project isn't in the database");
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
			fLog.debug("    Found persistence record");
			SVDBLoad loader = new SVDBLoad();
			InputStream in = null;
			boolean loaded = false;
			try {
				ZipInputStream zip_in = null;
				in = new FileInputStream(desc.getDBFile());
				
				if (desc.getDBFile().getName().endsWith(".zip")) {
					zip_in = new ZipInputStream(in);
					zip_in.getNextEntry();
					in = zip_in;
				}
				fLog.debug("Loading from file \"" + desc.getDBFile().getPath() + "\"");
				loader.load(index, in);
				loaded = true;
				
				in.close();
			} catch (Exception e) {
				e.printStackTrace();
				fLog.error("Failed to load index for project \"" + project + 
						"\" from file \"" + desc.getDBFile().getAbsolutePath() + 
						"\"", e);
				
				// Remove the DB file, since it's bad... 
				File db_file = desc.getDBFile();
				db_file.delete();
				
				// Remove this location so we don't get follow-on errors
				db_desc.remove(desc);
			} finally {
				if (in != null) {
					try {
						in.close();
					} catch (IOException e) {}
				}
			}
			
			return loaded;
		} else {
			fLog.debug("    Failed to find persistence record");
			return false;
		}
	}
	
	private void load_database_descriptors() {
		fLog.debug("load_database_descriptors");
		if (fDatabaseDir != null && fDatabaseDir.exists()) {
			SVDBLoad loader = new SVDBLoad();
			
			for (File d : fDatabaseDir.listFiles()) {
				if (d.isDirectory()) {
					String project_name = d.getName();
					List<SVDBPersistenceDescriptor> db_desc = 
						new ArrayList<SVDBPersistenceDescriptor>();
					
					fLog.debug("Load persistent data for project \"" + d.getName() + "\"");
					
					for (File f : d.listFiles()) {
						if (f.isFile() && 
								(f.getName().endsWith(".db") || f.getName().endsWith(".db.zip"))) {
							try {
								ZipInputStream zip_in = null;
								InputStream in = new FileInputStream(f);
								
								if (f.getName().endsWith(".zip")) {
									zip_in = new ZipInputStream(in);
									ZipEntry entry = zip_in.getNextEntry();
									fLog.debug("Open entry \"" + entry.getName() + "\" in db file \"" + 
											f.getAbsolutePath() + "\"");
									in = zip_in;
								}
								String base = loader.readBaseLocation(in);
								
								fLog.debug("Add index " + f.getAbsolutePath() + " with base=" + base);
								db_desc.add(
									new SVDBPersistenceDescriptor(f, base));
								
								in.close();
							} catch (Exception e) {
								fLog.error("Failed to read base location from index \"" + 
										f.getAbsolutePath() + "\" for project \"" + d.getName() + "\"", e);
								// If the file is corrupt, delete it
								f.delete();
							}
						}
					}
					
					fDatabaseDescMap.put(project_name, db_desc);
				}
			}
		} else {
			fLog.debug("Database location does not exist");
		}
	}
	

	/**
	 * Saves the state of loaded indexes to the state_location directory
	 */
	public void save_state() {
		fLog.debug("save_state()");
		
		for (String proj_name : fProjectIndexMap.keySet()) {
			save_state(proj_name, fProjectIndexMap.get(proj_name));
		}
		
		// Now, iterate through each saved database and clean up
		// any leftover saved-database files
		
	}
	
	private void save_state(String proj_name, List<ISVDBIndex> index_list) {
		SVDBDump dumper = new SVDBDump();
		List<SVDBPersistenceDescriptor>		db_list = fDatabaseDescMap.get(proj_name);
		
		if (fDatabaseDir == null) {
			fLog.debug("not saving state");
			return;
		}
		
		if (!fDatabaseDir.exists()) {
			if (!fDatabaseDir.mkdirs()) {
				fLog.error("cannot create database dir");
			}
		}
		
		for (ISVDBIndex index : index_list) {
			fLog.debug("fDatabaseDir=" + fDatabaseDir + "; proj_name=" + proj_name);
			
			if (proj_name == null) {
				fLog.error("proj_name null on : " + index.getClass().getName());
			}
			File proj_db_dir = new File(fDatabaseDir, proj_name);
			
			if (!proj_db_dir.exists()) {
				if (!(proj_db_dir.mkdirs())) {
					fLog.error("cannot create project db dir");
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
				
				fLog.debug("Saving index \"" + index + "\" for project \"" + 
						proj_db_dir.getName() + "\"");
				
				// Dump the database to disk
				try {
					ZipOutputStream zip_out = null;
					OutputStream out;
					
					if (index_file.getName().endsWith(".zip")) {
						index_file.delete(); // ensure we clear out the file
						out = new FileOutputStream(index_file);
						String entry_name = index_file.getName();
						entry_name = entry_name.substring(0, entry_name.length()-4);
						zip_out = new ZipOutputStream(out);
						zip_out.putNextEntry(new ZipEntry(entry_name));
					} else {
						 out = new FileOutputStream(index_file);						
					}

					if (zip_out != null) {
						dumper.dump(index, zip_out);
						zip_out.closeEntry();
						
						zip_out.flush();
						zip_out.close();
						out.close();
					} else {
						dumper.dump(index, out);
						out.flush();
						out.close();
					}
				} catch (Exception e) {
					fLog.error("Failed to save index \"" + 
							index.getBaseLocation() + "\" to persistence file \"" + 
							index_file.getAbsolutePath() + "\"", e);
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
		final boolean use_zip = true;
		if (!db_dir.exists()) {
			db_dir.mkdirs();
		}
		
		for (int i=0; i<1000000; i++) {
			File test = new File(db_dir, "index_" + i + ".db");
			File test_z = new File(db_dir, "index_" + i + ".db.zip");
			
			if (!test.exists() && !test_z.exists()) {
				if (use_zip) {
					return test_z;
				} else {
					return test;
				}
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
						fLog.error("Failed to create .exe class for IndexFactory " +
								"extension \"" + id + "\"", e);
					}
					break;
				}
			}
		}
		
		return ret;
	}
	
	
}
