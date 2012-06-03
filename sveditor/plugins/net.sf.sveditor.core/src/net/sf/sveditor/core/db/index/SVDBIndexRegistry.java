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

import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheFactory;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SubProgressMonitor;

/**
 * Central storage for leaf indexes. Provides a central place to locate
 * an index and supports persistence and loading
 * 
 * @author ballance
 *
 */
public class SVDBIndexRegistry  {
	public static final String							GLOBAL_PROJECT = "GLOBAL";
	
	private SVDBIndexCollectionMgr							fIndexCollectionMgr;
	private SVDBIndexCollection								fGlobalIndexMgr;
	private List<Reference<ISVDBIndex>>						fIndexList;
	private ISVDBIndexCacheFactory							fCacheFactory;
	private boolean										fAutoRebuildEn;
	private LogHandle										fLog;

	/**
	 * SVDBIndexRegistry constructor. Only intended to be called by
	 * 
	 * @param state_location
	 */
	public SVDBIndexRegistry() {
		this(false);
	}
	
	public SVDBIndexRegistry(boolean standalone_test_mode) {
		fIndexList = new ArrayList<Reference<ISVDBIndex>>();
		fLog = LogFactory.getLogHandle("SVDBIndexRegistry");
		fAutoRebuildEn = true;
		fIndexCollectionMgr = new SVDBIndexCollectionMgr();
	}
	
	public void setEnableAutoRebuild(boolean en) {
		fAutoRebuildEn = en;
		
		clearStaleIndexes();
		
		for (Reference<ISVDBIndex> i : fIndexList) {
			if (i.get() != null) {
				i.get().setEnableAutoRebuild(fAutoRebuildEn);
			}
		}
	}
	
	public SVDBIndexCollectionMgr getIndexCollectionMgr() {
		return fIndexCollectionMgr;
	}
	
	public void init(ISVDBIndexCacheFactory cache_factory) {
		fCacheFactory = cache_factory;
		fIndexList.clear();
		
		fGlobalIndexMgr = getGlobalIndexMgr();
	}

	public void test_init(ISVDBIndexCacheFactory cache_factory) {
		fCacheFactory = cache_factory;
		fIndexList.clear();
	}
	
	public List<ISVDBIndex> getAllProjectLists() {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				if (i.get() != null) { 
					ret.add(i.get());
				}
			}
		}
		return ret ;
	}

	public List<ISVDBIndex> getProjectIndexList(String project) {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		clearStaleIndexes();
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				if (i.get() != null && i.get().getProject().equals(project)) {
					ret.add(i.get());
				}
			}
		}
		
		return ret;
	}
	
	public List<ISVDBIndex> getIndexList() {
		List<ISVDBIndex> ret = new ArrayList<ISVDBIndex>();
		
		clearStaleIndexes();
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				if (i.get() != null) {
					ret.add(i.get());
				}
			}
		}
		
		return ret;
	}
	
	public SVDBIndexCollection getGlobalIndexMgr() {
		if (fGlobalIndexMgr == null) {
			fGlobalIndexMgr = new SVDBIndexCollection(fIndexCollectionMgr, GLOBAL_PROJECT);
			
			// Ensure the global index has access to the built-in types
			ISVDBIndex index = findCreateIndex(
					new NullProgressMonitor(),
					SVDBIndexRegistry.GLOBAL_PROJECT, 
					SVCorePlugin.SV_BUILTIN_LIBRARY, 
					SVDBPluginLibIndexFactory.TYPE, null);
			if (index != null) {
				fGlobalIndexMgr.addPluginLibrary(index);
			}
		}
		return fGlobalIndexMgr;
	}

	@Deprecated
	public ISVDBIndex findCreateIndex(
			String 					project, 
			String 					base_location, 
			String 					type,
			Map<String, Object>		config) {
		return findCreateIndex(new NullProgressMonitor(), project,
				base_location, type, config);
	}
	
	public ISVDBIndex findCreateIndex(
			IProgressMonitor		monitor,
			String 					project, 
			String 					base_location, 
			String 					type,
			ISVDBIndexCache			cache,
			Map<String, Object>		config) {
		ISVDBIndex ret = null;
		
		fLog.debug("findCreateIndex: " + base_location + " ; " + type);
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				ISVDBIndex index = i.get();
				if (index != null && index.getProject().equals(project) &&
						index.getBaseLocation().equals(base_location) &&
						index.getTypeID().equals(type)) {
					ret = index;
					break;
				}
			}
		}
		
		if (ret == null) {
			fLog.debug("    Index does not exist -- creating");
			// See about creating a new index
			ISVDBIndexFactory factory = findFactory(type);
			
			ret = factory.createSVDBIndex(project, base_location, cache, config);
			ret.setEnableAutoRebuild(fAutoRebuildEn);
			
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			ret.init(m);
			
			synchronized (fIndexList) {
				fIndexList.add(new WeakReference<ISVDBIndex>(ret));
			}
		} else {
			fLog.debug("    Index already exists");
		}
		
		return ret;
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
			IProgressMonitor		monitor,
			String 					project, 
			String 					base_location, 
			String 					type,
			Map<String, Object>		config) {
		ISVDBIndex ret = null;
		
		fLog.debug("findCreateIndex: " + base_location + " ; " + type);
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				ISVDBIndex index = i.get();
				if (index != null && index.getProject().equals(project) &&
						index.getBaseLocation().equals(base_location) &&
						index.getTypeID().equals(type)) {
					ret = index;
					break;
				}
			}
		}
		
		if (ret == null) {
			fLog.debug("    Index does not exist -- creating");
			// See about creating a new index
			ISVDBIndexFactory factory = findFactory(type);
			ISVDBIndexCache cache = null;
			
			if (type.equals(SVDBShadowIndexFactory.TYPE)) {
				cache = new InMemoryIndexCache();
			} else {
				cache = fCacheFactory.createIndexCache(project, base_location);
			}
			
			ret = factory.createSVDBIndex(project, base_location, cache, config);
			ret.setEnableAutoRebuild(fAutoRebuildEn);
			
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			ret.init(m);
			
			synchronized (fIndexList) {
				fIndexList.add(new WeakReference<ISVDBIndex>(ret));
			}
		} else {
			fLog.debug("    Index already exists");
		}
		
		return ret;
	}

	public ISVDBIndex findCreateIndex(
			String 					project, 
			String 					base_location, 
			String 					type,
			ISVDBIndexFactory		factory,
			Map<String, Object>		config) {
		return findCreateIndex(new NullProgressMonitor(), project,
				base_location, type, factory, config);
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
			IProgressMonitor		monitor,
			String 					project, 
			String 					base_location, 
			String 					type,
			ISVDBIndexFactory		factory,
			Map<String, Object>		config) {
		ISVDBIndex ret = null;
		
		fLog.debug("findCreateIndex: " + base_location + " ; " + type);
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				ISVDBIndex index = i.get();
				if (index != null && index.getProject().equals(project) &&
						index.getBaseLocation().equals(base_location) &&
						index.getTypeID().equals(type)) {
					ret = index;
					break;
				}
			}
		}
		
		if (ret == null) {
			fLog.debug("    Index does not exist -- creating");
			ISVDBIndexCache cache = fCacheFactory.createIndexCache(project, base_location);
			
			// See about creating a new index
			ret = factory.createSVDBIndex(project, base_location, cache, config);
			ret.setEnableAutoRebuild(fAutoRebuildEn);
			
			SubProgressMonitor m = new SubProgressMonitor(monitor, 1);
			ret.init(m);
			
			synchronized (fIndexList) {
				fIndexList.add(new WeakReference<ISVDBIndex>(ret));
			}
		} else {
			fLog.debug("    Index already exists");
		}
		
		return ret;
	}
	
	public void rebuildIndex(String project) {
		fLog.debug("rebuildIndex \"" + project + "\"");
		
		clearStaleIndexes();
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				ISVDBIndex index = i.get();
				if (index != null && index.getProject().equals(project)) {
					index.rebuildIndex();
				}
			}
		}
	}

	/**
	 * Saves the state of loaded indexes to the state_location directory
	 */
	public void save_state() {
		fLog.debug("save_state()");
		
		synchronized (fIndexList) {
			for (Reference<ISVDBIndex> i : fIndexList) {
				ISVDBIndex index = i.get();
				if (index != null) {
					index.dispose();
				}
			}
		}
		
		if (fCacheFactory != null) {
			List<ISVDBIndexCache> cache_l = new ArrayList<ISVDBIndexCache>();
			synchronized (fIndexList) {
				for (Reference<ISVDBIndex> i : fIndexList) {
					ISVDBIndex index = i.get();
					if (index != null && !cache_l.contains(index.getCache()) && index.getCache() != null) {
						cache_l.add(index.getCache());
					}
				}
			}
			
			// Compact the cache-storage area
			fCacheFactory.compactCache(cache_l);
		}
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
	
	private void clearStaleIndexes() {
		synchronized (fIndexList) {
			for (int i=0; i<fIndexList.size(); i++) {
				if (fIndexList.get(i).get() == null) {
					System.out.println("Removing stale index");
					fIndexList.remove(i);
					i--;
				}
			}
		}
	}
	
}
