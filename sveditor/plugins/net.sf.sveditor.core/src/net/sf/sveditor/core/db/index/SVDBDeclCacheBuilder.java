package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.ISVParserTypeListener;
import net.sf.sveditor.core.preproc.ISVPreProcListener;
import net.sf.sveditor.core.preproc.SVPreProcEvent;

/**
 * Listener that builds the declaration cache
 * 
 * @author ballance
 *
 */
public class SVDBDeclCacheBuilder implements 
	ISVParserTypeListener,
	ISVPreProcListener,
	ILogLevelListener {
	private ISVDBDeclCacheInt			fDeclCache;
	private int							fRootFileId;
	private List<Integer>				fScopeStack;
	private static final List<Integer>	fEmptyScopeStack = new ArrayList<Integer>();
	private List<SVDBDeclCacheItem>		fDeclList;
	private LogHandle					fLog;
	private boolean						fDebugEn;
	
	public SVDBDeclCacheBuilder(
			List<SVDBDeclCacheItem> decl_list,
			ISVDBDeclCacheInt		decl_cache,
			int						rootfile_id) {
		fDeclCache = decl_cache;
		fRootFileId = rootfile_id;
		fScopeStack = new ArrayList<Integer>();
		fDeclList = decl_list;
		fDeclList.clear();
		fLog = LogFactory.getLogHandle("SVDBDeclCacheBuilder");
		fLog.addLogLevelListener(this);
		logLevelChanged(fLog);
	}
	
	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = (handle.getDebugLevel() > 0);
	}
	
	private static final Set<SVDBItemType>		fPackageScopeTypes;
	
	static {
		fPackageScopeTypes = new HashSet<SVDBItemType>();
		fPackageScopeTypes.add(SVDBItemType.Function);
		fPackageScopeTypes.add(SVDBItemType.Task);
		fPackageScopeTypes.add(SVDBItemType.VarDeclItem);
	}
	
	private SVDBDeclCacheItem parent_item() {
		if (fScopeStack.size() > 0) {
			return fDeclList.get(fScopeStack.get(fScopeStack.size()-1));
		} else {
			return null;
		}
	}

	@Override
	public void enter_type_scope(ISVDBItemBase item) {
		if (fDebugEn) {
			fLog.debug("enter_type_scope: " + item.getType());
		}
		// We save some types only if they are at package level
		if (item instanceof ISVDBNamedItem && (
				!item.getType().isElemOf(fPackageScopeTypes) ||
				fScopeStack.size() == 0 ||
				parent_item().getType() == SVDBItemType.PackageDecl)) {
			String name = ((ISVDBNamedItem)item).getName();
			
			SVDBDeclCacheItem cache_i = new SVDBDeclCacheItem(
					fDeclCache,
					fRootFileId,
					SVDBLocation.unpackFileId(item.getLocation()),
					fScopeStack,
					name,
					item.getType(),
					false);
			fScopeStack.add(fDeclList.size());
			fDeclList.add(cache_i);
			
			if (item.getType() == SVDBItemType.TypedefStmt) {
				SVDBTypedefStmt td = (SVDBTypedefStmt)item;
				if (td.getTypeInfo() != null &&
						td.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
					SVDBTypeInfoEnum e = (SVDBTypeInfoEnum)td.getTypeInfo();
					for (SVDBTypeInfoEnumerator ev : e.getEnumerators()) {
						SVDBDeclCacheItem ev_cache_i = new SVDBDeclCacheItem(
								fDeclCache,
								fRootFileId,
								SVDBLocation.unpackFileId(item.getLocation()),
								fScopeStack,
								ev.getName(),
								ev.getType(),
								false);
						fDeclList.add(ev_cache_i);
					}
				}
			}
		}
	}

	@Override
	public void leave_type_scope(ISVDBItemBase item) {
		if (fDebugEn) {
			fLog.debug("leave_type_scope: " + item.getType());
		}
		if (fScopeStack.size() > 0) {
			SVDBDeclCacheItem ci = fDeclList.get(fScopeStack.get(fScopeStack.size()-1));
			
			if (ci.getType() == item.getType()) {
				if (item instanceof ISVDBNamedItem) {
					if (((ISVDBNamedItem)item).getName().equals(ci.getName())) {
						fScopeStack.remove(fScopeStack.size()-1);
					}
				} else {
					fScopeStack.remove(fScopeStack.size()-1);
				}
			}
		}
	}

	@Override
	public void preproc_event(SVPreProcEvent ev) {
		if (ev.type == SVPreProcEvent.Type.Define) {
			if (fDebugEn) {
				fLog.debug("DeclCacheBuilder: Add Define \"" + 
					((SVDBMacroDef)ev.decl).getName() + "\"");
			}
			SVDBDeclCacheItem cache_i = new SVDBDeclCacheItem(
					fDeclCache,
					fRootFileId,
					SVDBLocation.unpackFileId(ev.decl.getLocation()),
					fEmptyScopeStack,
					((SVDBMacroDef)ev.decl).getName(),
					ev.decl.getType(),
					true);
			fDeclList.add(cache_i);
		} else if (ev.type == SVPreProcEvent.Type.EnterFile) {
			if (fDebugEn) {
				fLog.debug("EnterFile: " + ev.text);
			}
		} else if (ev.type == SVPreProcEvent.Type.LeaveFile) {
			if (fDebugEn) {
				fLog.debug("LeaveFile: " + ev.text);
			}
		}
	}

}
