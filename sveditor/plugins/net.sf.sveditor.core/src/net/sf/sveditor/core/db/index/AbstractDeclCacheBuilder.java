package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBFileTreeMacroList;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.IDocCommentParser;
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
	// Number of scopes pushed that are 'disabled'
	private int							fDisabledDepth;
	// Contains a stack of the saved scope IDs
	private List<Integer>				fScopeStack;
	private List<ISVDBItemBase>			fAllScopeStack;
	private static final List<Integer>	fEmptyScopeStack = new ArrayList<Integer>();
	private List<SVDBDeclCacheItem>		fDeclList;
	private Set<Integer>				fIncludedFilesSet;
	private Set<String>					fMissingIncludes;
	private IDocCommentParser 			fDocCommentParser;
	private LogHandle					fLog;
	private boolean						fDebugEn;
	private SVDBFileTree				fFileTree;
	private Stack<SVDBFileTree>			fFileTreeStack;
//	private List<SVDBMarker>			fMarkers;
	private static final Set<String>	fTaskTags;
	
	static {
		fTaskTags = new HashSet<String>();
		fTaskTags.add("TODO");
		fTaskTags.add("FIXME");
	}
	
	public SVDBDeclCacheBuilder() {
		this(
				new ArrayList<SVDBDeclCacheItem>(),
				null,
				new HashSet<Integer>(),
				new HashSet<String>(),
				-1);
	}
	
	public SVDBDeclCacheBuilder(
			List<SVDBDeclCacheItem> decl_list,
			ISVDBDeclCacheInt		decl_cache,
			Set<Integer>			included_files,
			Set<String>				missing_includes,
			int						rootfile_id) {
		fDeclCache = decl_cache;
		fRootFileId = rootfile_id;
		fDisabledDepth = 0;
		fDocCommentParser = new DocCommentParser();
		fScopeStack = new ArrayList<Integer>();
		fAllScopeStack = new ArrayList<ISVDBItemBase>();
		fDeclList = decl_list;
		fDeclList.clear();
		fIncludedFilesSet = included_files;
		fIncludedFilesSet.clear();
		fMissingIncludes = missing_includes;
		fMissingIncludes.clear();
		fFileTreeStack = new Stack<SVDBFileTree>();
//		fMarkers = new ArrayList<SVDBMarker>();
		fLog = LogFactory.getLogHandle("SVDBDeclCacheBuilder");
		fLog.addLogLevelListener(this);
		logLevelChanged(fLog);
	}
	
	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = (handle.getDebugLevel() > 0);
	}
	
	private static final Set<SVDBItemType>		fGlobalScopeItems;
	
	static {
		fGlobalScopeItems = new HashSet<SVDBItemType>();
		fGlobalScopeItems.add(SVDBItemType.Function);
		fGlobalScopeItems.add(SVDBItemType.Task);
		fGlobalScopeItems.add(SVDBItemType.VarDeclItem);
		fGlobalScopeItems.add(SVDBItemType.TypedefStmt);
		fGlobalScopeItems.add(SVDBItemType.ClassDecl);
		fGlobalScopeItems.add(SVDBItemType.PackageDecl);
		fGlobalScopeItems.add(SVDBItemType.Covergroup);
		fGlobalScopeItems.add(SVDBItemType.InterfaceDecl);
		fGlobalScopeItems.add(SVDBItemType.ModuleDecl);
		fGlobalScopeItems.add(SVDBItemType.ProgramDecl);
	}
	
	public SVDBFileTree getFileTree() {
		return fFileTree;
	}
	
//	private ISVDBItemBase parent_item() {
//		if (fScopeStack.size() > 0) {
//			return fScopeStack.get(fScopeStack.size()-1);
//		} else {
//			return null;
//		}
//	}
	
	private boolean should_add(ISVDBItemBase item) {
		if (fDisabledDepth > 0) {
			return false;
		} else if (fScopeStack.size() == 0) {
			// Global scope
			return item.getType().isElemOf(fGlobalScopeItems);
		} else {
			return true;
		}
	}
	
	@Override
	public void enter_type_scope(ISVDBItemBase item) {
		if (fDebugEn) {
			fLog.debug("enter_type_scope: " + item.getType() + " " + SVDBItem.getName(item) + " " + fDisabledDepth);
//			try {
//				throw new Exception("enter_type_scope");
//			} catch (Exception e) {
//				e.printStackTrace();
//			}
		}
		fAllScopeStack.add(item);
	
		// Once we enter a scope where indexing is disabled,
		// we stay disabled
		if (fDisabledDepth == 0 && should_add(item)) {
			String name = ((ISVDBNamedItem)item).getName();
		
			if (fDebugEn) {
				fLog.debug("INDEX: " + name + " " + item.getType());
			}
			
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
				if (td.getTypeInfo() != null) {
					if (td.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
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
					} else if (td.getTypeInfo().getType() == SVDBItemType.TypeInfoStruct) {
//						SVDBDeclCacheItem cache_i = new SVDBDeclCacheItem(
//								fDeclCache,
//								fRootFileId,
//								SVDBLocation.unpackFileId(item.getLocation()),
//								fScopeStack,
//								name,
//								item.getType(),
//								false);
//						
					}
				}
			}
			
			if (item.getType() != SVDBItemType.PackageDecl) {
				fDisabledDepth++;
				if (fDebugEn) {
					fLog.debug("INDEX: fDisableDepth => " + fDisabledDepth);
				}
				if (fDebugEn) {
					fLog.debug("INDEX: toggling to disabled on " + item.getType() + " " + SVDBItem.getName(item));
				}
			}
		} else {
			if (fDisabledDepth == 0) {
				if (fDebugEn) {
					fLog.debug("INDEX: toggling to disabled on " + item.getType() + " " + SVDBItem.getName(item));
				}
			}
			fDisabledDepth++;
			if (fDebugEn) {
				fLog.debug("INDEX: fDisableDepth => " + fDisabledDepth);
			}
		}
	}

	@Override
	public void leave_type_scope(ISVDBItemBase item) {
		if (fDebugEn) {
			fLog.debug("leave_type_scope: " + item.getType() + " " + fDisabledDepth);
//			try {
//				throw new Exception("leave_type_scope");
//			} catch (Exception e) {
//				e.printStackTrace();
//			}
		}
		
		if (fAllScopeStack.size() > 0) {
			if (fAllScopeStack.get(fAllScopeStack.size()-1).getType() != item.getType()) {
				System.out.println("AllScopeStack out-of-sync: expect " + item.getType() + 
						" receive " + fAllScopeStack.get(fAllScopeStack.size()-1).getType());
			}
			fAllScopeStack.remove(fAllScopeStack.size()-1);
		} else {
			System.out.println("AllScopeStack out-of-sync on " + item.getType());
		}
		if (fDisabledDepth > 0) {
			fDisabledDepth--;
			if (fDebugEn) {
				fLog.debug("INDEX: fDisableDepth => " + fDisabledDepth);
			}
			
			if (fDisabledDepth == 0) {
				if (fDebugEn) {
					fLog.debug("INDEX: toggling to enabled on " + item.getType() + " " + SVDBItem.getName(item));
				}
			}
		}
		
		if (fDisabledDepth == 0) {
			if (fScopeStack.size() > 0) {
//			SVDBDeclCacheItem ci = fDeclList.get(fScopeStack.get(fScopeStack.size()-1));
			fScopeStack.remove(fScopeStack.size()-1);
			
//			if (ci.getType() == item.getType()) {
//				if (item instanceof ISVDBNamedItem) {
//					if (((ISVDBNamedItem)item).getName().equals(ci.getName())) {
//						fScopeStack.remove(fScopeStack.size()-1);
//					}
//				} else {
//				}
//			}
			} else {
				System.out.println("Internal Error: fScopeStack.size == 0 on " + item.getType());
			}
		}
	}

	@Override
	public void preproc_event(SVPreProcEvent ev) {
		switch (ev.type) {
		case Define: {
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
			fFileTreeStack.peek().getSVDBFile().addChildItem(
					(SVDBMacroDef)ev.decl);
			fFileTreeStack.peek().addToMacroSet(
					(SVDBMacroDef)ev.decl);
		} break;
		
		case MacroRef: {
			fFileTreeStack.peek().fReferencedMacros.remove(ev.text);
			if (ev.decl != null) {
				fFileTreeStack.peek().fReferencedMacros.put(
						ev.text, ((SVDBMacroDef)ev.decl).getDef());
			} else {
				fFileTreeStack.peek().fReferencedMacros.put(ev.text, null);
			}
		} break;
	
		case EnterFile: {
			if (fDebugEn) {
				fLog.debug("EnterFile: " + ev.text + " " + ev.file_id);
			}
			SVDBFileTree ft = new SVDBFileTree(ev.text);
			SVDBFile file = new SVDBFile(ev.text);
			file.setLocation(ev.loc);
			ft.setSVDBFile(file);
			if (fFileTreeStack.size() > 0) {
				fFileTreeStack.peek().addIncludedFileTree(ft);
			} else {
				fFileTree = ft; // capture the root filetree
			}
			if (!fFileTreeStack.empty()) {
				ft.setParent(fFileTreeStack.peek());
				// TODO:
//				fFileTreeStack.peek().addIncludedFileTree(ft);
			}
			fFileTreeStack.push(ft);
			fIncludedFilesSet.add(ev.file_id);
		} break;
		
		case LeaveFile: {
			if (fDebugEn) {
				fLog.debug("LeaveFile: " + ev.text);
			}
			fFileTreeStack.pop();
		} break;
		case MissingInclude: {
			// Only deal with the leaf of missing includes
			String path = SVFileUtils.getPathLeaf(ev.text);
		
			fMissingIncludes.add(path);
		} break;
		case Comment: {
			process_comment(ev.text, ev.loc);
		} break;
		case Marker: {
			fFileTreeStack.peek().fMarkers.add(
					(SVDBMarker)ev.decl);
		} break;
		
		case Include: {
			fFileTreeStack.peek().getSVDBFile().addChildItem(
					(SVDBInclude)ev.decl);
			
			SVDBFileTree ft_i = new SVDBFileTree(ev.text);
			ft_i.setSVDBFile(new SVDBFile(ev.text));
			ft_i.setParent(fFileTreeStack.peek());
			fFileTreeStack.peek().addIncludedFileTree(ft_i);
//			for (SVDBFileTreeMacroList ml : defs.second()) {
//				for (SVDBMacroDef m : ml.getMacroList()) {
//					ft_i.addToMacroSet(m);
//				}
//			}			
		} break;
		
		}
	}

	private void process_comment(String comment, long loc) {
		Tuple<String,String> dc = new Tuple<String, String>(null, null);
		IDocCommentParser.CommentType type = fDocCommentParser.isDocCommentOrTaskTag(comment, dc) ;
		if (type != null && type != IDocCommentParser.CommentType.None) {
			String tag = dc.first();
			String title = dc.second();
//			SVPreProc2InputData in = fInputCurr;
			
			boolean is_task = fTaskTags.contains(tag);

			if (type == IDocCommentParser.CommentType.TaskTag && is_task) {
				// Actually a task marker
				String msg = tag + " " + title;
				SVDBMarker m = new SVDBMarker(MarkerType.Task, MarkerKind.Info, msg);

				// Fix the offset to the TODO in case it is not the first thing in a comment... typically in a multi-line comment
				int fileid = SVDBLocation.unpackFileId(loc);
				int line   = SVDBLocation.unpackLineno(loc);
				int pos    = SVDBLocation.unpackPos(loc);
				String lines[] = comment.split("\\n");
				for (String cl: lines)  {
					if (cl.contains(tag))  {
						break;
					}
					else  {
						line ++;
					}
				}
				loc = SVDBLocation.pack(fileid, line, pos);

				// Set location
				m.setLocation(loc);
				// TODO:
				fFileTreeStack.peek().fMarkers.add(m);
			} else if (type == IDocCommentParser.CommentType.DocComment && is_task) {
				String msg = tag + ": " + title;
				SVDBMarker m = new SVDBMarker(MarkerType.Task, MarkerKind.Info, msg);
				
				// Fix the offset to the TODO in case it is not the first thing in a comment... typically in a multi-line comment
				int fileid = SVDBLocation.unpackFileId(loc);
				int line   = SVDBLocation.unpackLineno(loc);
				int pos    = SVDBLocation.unpackPos(loc);
				String lines[] = comment.split("\\n");
				for (String cl: lines)  {
					if (cl.contains(tag))  {
						break;
					}
					else  {
						line ++;
					}
				}
				loc = SVDBLocation.pack(fileid, line, pos);

				// Set location
				m.setLocation(loc);
				// TODO:
				fFileTreeStack.peek().fMarkers.add(m);
			} else if (DocTopicManager.singularKeywordMap.containsKey(tag.toLowerCase())) {
				// Really a doc comment
				SVDBDocComment doc_comment = new SVDBDocComment(title, comment);

				doc_comment.setLocation(loc);
				fFileTreeStack.peek().getSVDBFile().addChildItem(doc_comment);
			}
		} 		
	}
}
