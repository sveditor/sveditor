package net.sf.sveditor.core.preproc;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocTopicManager;
import net.sf.sveditor.core.docs.IDocCommentParser;

public class SVPreProcFileTreeBuilder implements ISVPreProcListener {
	private Set<String>								fTaskTags;
	private IDocCommentParser   					fDocCommentParser;
	private Stack<SVDBFileTree>						fFileTreeStack;
	private SVDBFileTree							fRootFileTree;
	
	public SVPreProcFileTreeBuilder(SVPreProcessor preproc) {
		fTaskTags = new HashSet<String>();
		fTaskTags.add("TODO");
		fTaskTags.add("FIXME");		
	
		fDocCommentParser = new DocCommentParser();
		
		fFileTreeStack = new Stack<SVDBFileTree>();
		
		if (preproc != null) {
			preproc.addListener(this);
		}
	} 
	
	public SVPreProcFileTreeBuilder() {
		this(null);
	}

	@Override
	public void preproc_event(SVPreProcEvent event) {
		switch (event.type) {
		case Comment: 
			comment(event.text, event.loc, event.ft); 
			break;
		case Define: 
			define(event.ft, (SVDBMacroDef)event.decl); 
			break;
		case EnterFile: 
			enter_file(event.ft); 
			break;
		case LeaveFile: 
			leave_file(event.ft); 
			break;
		case Include: 
			include(event.ft, (SVDBInclude)event.decl); 
			break;
		case Marker: 
			marker(event.ft, (SVDBMarker)event.decl); 
			break;
		}
		// TODO Auto-generated method stub
		
	}
	
	public SVDBFileTree getFileTree() {
		return fRootFileTree;
	}
	
	private void comment(String comment, long start, SVDBFileTree ft) {
		Tuple<String,String> dc = new Tuple<String, String>(null, null);
		IDocCommentParser.CommentType type = fDocCommentParser.isDocCommentOrTaskTag(comment, dc) ;
		if (type != null && type != IDocCommentParser.CommentType.None) {
			String tag = dc.first();
			String title = dc.second();
			long loc = start;
			
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
				if (ft != null) {
					ft.fMarkers.add(m);
				}
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
				if (ft != null) {
					ft.fMarkers.add(m);
				}
			} else if (DocTopicManager.singularKeywordMap.containsKey(tag.toLowerCase())) {
				// Really a doc comment
				SVDBDocComment doc_comment = new SVDBDocComment(title, comment);

				doc_comment.setLocation(loc);
				if (ft != null) {
					ft.getSVDBFile().addChildItem(doc_comment);
				}
			}
		} 		
	}

	private void define(SVDBFileTree ft, SVDBMacroDef m) {
		if (ft != null && ft.getSVDBFile() != null) {
			ft.getSVDBFile().addChildItem(m);
			ft.addToMacroSet(m);
		}		
	}
	
	private void enter_file(SVDBFileTree ft) {
		if (fFileTreeStack.size() > 0) {
			ft.setParent(fFileTreeStack.peek());
			fFileTreeStack.peek().addIncludedFileTree(ft);
		} else {
			fRootFileTree = ft;
		}
		
		fFileTreeStack.push(ft);
	}
	
	private void leave_file(SVDBFileTree ft) {
		fFileTreeStack.pop();
	}
	
	private void include(SVDBFileTree ft, SVDBInclude inc) {
		if (ft != null) {
			ft.getSVDBFile().addChildItem(inc);

			// defs comes from the fIncFileProvider.findCachedIncFile()
			//		SVDBFileTree ft_i = new SVDBFileTree(defs.first());
			//		ft_i.setParent(ft);
			//		ft.addIncludedFileTree(ft_i);
			//
			//		for (SVDBFileTreeMacroList ml : defs.second()) {
			//			for (SVDBMacroDef m : ml.getMacroList()) {
			//				ft_i.addToMacroSet(m);
			//			}
			//		}		


			ft.getSVDBFile().addChildItem(inc);
		}
	}
	
	private void marker(SVDBFileTree ft, SVDBMarker m) {
		if (ft != null) {
			ft.fMarkers.add(m);
		}
	}
}
