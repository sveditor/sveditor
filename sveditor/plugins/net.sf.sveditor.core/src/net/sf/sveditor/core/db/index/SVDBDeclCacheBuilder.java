package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;
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
	ISVPreProcListener {
	private ISVDBDeclCacheInt			fDeclCache;
	private int							fRootFileId;
	private List<Integer>				fScopeStack;
	private static final List<Integer>	fEmptyScopeStack = new ArrayList<Integer>();
	private List<SVDBDeclCacheItem>		fDeclList;
	
	public SVDBDeclCacheBuilder(
			List<SVDBDeclCacheItem> decl_list,
			ISVDBDeclCacheInt		decl_cache,
			int						rootfile_id) {
		fDeclCache = decl_cache;
		fRootFileId = rootfile_id;
		fScopeStack = new ArrayList<Integer>();
		fDeclList = decl_list;
		fDeclList.clear();
	}

	@Override
	public void enter_type_scope(ISVDBItemBase item) {
		if (item instanceof ISVDBNamedItem) {
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
		}
	}

	@Override
	public void leave_type_scope(ISVDBItemBase item) {
		if (item instanceof ISVDBNamedItem) {
			fScopeStack.remove(fScopeStack.size()-1);
		}
	}

	@Override
	public void preproc_event(SVPreProcEvent ev) {
		if (ev.type == SVPreProcEvent.Type.Define) {
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
			System.out.println("Enter: " + ev.text);
		} else if (ev.type == SVPreProcEvent.Type.LeaveFile) {
			System.out.println("Leave: " + ev.text);
		}
	}

}
