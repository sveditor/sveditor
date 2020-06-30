/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.search;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBDocComment;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class SVDBFindDocComment {
	private ISVDBIndexIterator			fIndexIt;
	private LogHandle					fLog;


	public SVDBFindDocComment(ISVDBIndexIterator index_it) {
		fIndexIt = index_it;
		fLog = LogFactory.getLogHandle("SVDBFindDocComment");
	}
	
	/**
	 * Find the doc comment corresponding to the specified item
	 * 
	 * @param item
	 * @return
	 */
	public SVDBDocComment find(IProgressMonitor monitor, ISVDBItemBase item) {
		SVDBDocComment comment = null;

		// Must reach the file scope
		ISVDBItemBase p = item;
		while (p != null && p.getType() != SVDBItemType.File) {
			if (p instanceof ISVDBChildItem) {
				p = ((ISVDBChildItem)p).getParent();
			} else {
				p = null;
				break;
			}
		}
		
		if (p == null) {
			fLog.debug(
					ILogLevel.LEVEL_MID,
					String.format("Failed to find file for type(%s)",
					SVDBItem.getName(item)));
			return null;
		}
		
		SVDBFile pp_file = fIndexIt.findPreProcFile(monitor, ((SVDBFile)p).getFilePath());
		
		if (pp_file != null) {
			comment = find_comment(pp_file, item);
		} else {
			fLog.debug(ILogLevel.LEVEL_MID, "Failed to find pre-proc file " + 
					((SVDBFile)p).getFilePath());
			/*
			for (String path : fIndexIt.getFileList(new NullProgressMonitor())) {
				fLog.debug(ILogLevel.LEVEL_MAX, "  Path: " + path);
			}
			 */
		}
	
		return comment;
	}
	
	private String cleanCommentNameForMatch(String commentName) {
		String cleaned = commentName.replaceAll("[\\t\\s]*#.*","") ;
		return cleaned ;
	}

	private SVDBDocComment find_comment(ISVDBChildParent p, ISVDBItemBase item) {
		SVDBDocComment comment = null;
		for (ISVDBChildItem child: p.getChildren()) {
			fLog.debug("Find (" + SVDBItem.getName(item) + ") Child: " + SVDBItem.getName(child));
			if (child.getType() == SVDBItemType.DocComment) {
				SVDBDocComment tryDocCom = (SVDBDocComment)child;
				String nameCleaned = cleanCommentNameForMatch(tryDocCom.getName()) ;
				if (nameCleaned.equals(SVDBItem.getName(item))) {
					fLog.debug(ILogLevel.LEVEL_MID,
							String.format("Found doc comment for(%s)", SVDBItem.getName(item)));
					comment = tryDocCom;
					break;
				}
			} else if (child instanceof ISVDBChildParent) {
				if ((comment = find_comment((ISVDBChildParent)child, item)) != null) {
					break;
				}
			}
		}
		return comment;
	}
}
