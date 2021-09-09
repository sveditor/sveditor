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
package org.sveditor.core.builder;

import java.util.Stack;

import org.sveditor.core.preproc.ISVPreProcFileMapper;
import org.sveditor.core.preproc.ISVPreProcOutputFileChangeListener;

public class SVBuilderPreProcTracker implements ISVPreProcOutputFileChangeListener {
	private ISVBuilderOutput			fOut;
	private ISVPreProcFileMapper		fMapper;
	private Stack<Integer>				fFileStack;
	private StringBuilder				fIndent;
	
	public SVBuilderPreProcTracker(
			ISVBuilderOutput			out,
			ISVPreProcFileMapper		mapper) {
		fOut = out;
		fMapper = mapper;
		fFileStack = new Stack<Integer>();
		fIndent = new StringBuilder("  ");
	}

	@Override
	public void fileChanged(int old_id, int new_id) {
//		fOut.note("File Changed: " + old_id + " " + new_id + " (" + fFileStack.size() + ")");
		if (fFileStack.size() > 0) {
			int top = fFileStack.pop();

			if (fFileStack.size() == 0 || fFileStack.peek() != new_id) {
				// Entering a new level
				fFileStack.push(top);
				fFileStack.push(new_id);
				fIndent.append("  ");
				fOut.note(fIndent.toString() + "Parse: " + fMapper.mapFileIdToPath(new_id));
			} else {
				// new_id was already on the stack
				// We're just moving up the stack
				fIndent.setLength(fIndent.length()-2);
			}
//				// Only one thing on the stack. 
//				if (top != new_id) {
//					// Entering a new file
//					fFileStack.push(new_id);
//					fIndent.append("  ");
//					fOut.note(fIndent.toString() + "Parse: " + fMapper.mapFileIdToPath(new_id));
//				} // Otherwise, we're done
//			} else {
//				if (fFileStack.peek() == new_id) {
//					// Heading up ; the new file was the one we were just in
//					fIndent.setLength(fIndent.length()-2);
//				} else {
//					// heading down
//					fFileStack.push(new_id);
//					fIndent.append("  ");
//					fOut.note(fIndent.toString() + "Parse: " + fMapper.mapFileIdToPath(new_id));
//				}
//			}
//			if (fFileStack.peek() == new_id) {
//				// Going back to previous inclusion level
//				fFileStack.pop();
//				fIndent.setLength(fIndent.length()-2);
//			} else {
//				// Entering a new level
//				fFileStack.push(new_id);
//				fOut.note(fIndent.toString() + "Parse: " + fMapper.mapFileIdToPath(new_id));
//			}
		} else {
			// Initial
			fOut.note(fIndent.toString() + "Parse: " + fMapper.mapFileIdToPath(new_id));
			fFileStack.push(old_id);
			fFileStack.push(new_id);
		}
	}
	
}
