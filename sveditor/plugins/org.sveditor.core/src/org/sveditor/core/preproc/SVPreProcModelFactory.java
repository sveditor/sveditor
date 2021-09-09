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
package org.sveditor.core.preproc;

import java.io.InputStream;
import java.util.Stack;

import org.sveditor.core.StringInputStream;
import org.sveditor.core.Tuple;
import org.sveditor.core.preproc.PreProcEvent.Type;

/**
 * Used to construct 
 * @author ballance
 *
 */
public class SVPreProcModelFactory implements IPreProcListener {
	private ISVStringPreProcessor			fPreProc;
	private Stack<SVPreProcModelNode>		fModelStack;
	private SVPreProcModelNode				fRoot;
	
	public SVPreProcModelFactory(ISVStringPreProcessor preproc) {
		fPreProc = preproc;
		fModelStack = new Stack<SVPreProcModelNode>();
	}
	
	public Tuple<SVPreProcModelNode, String> build(InputStream in) {
		fModelStack.clear();
		fRoot = null;
	
		fPreProc.setEmitLineDirectives(false);
		fPreProc.addListener(this);
		String result = fPreProc.preprocess(in);
		fPreProc.removeListener(this);
		
		// Traverse event stack to build the expansion model 
		
		return new Tuple<SVPreProcModelNode, String>(fRoot, result);
	}
	
	public Tuple<SVPreProcModelNode, String> build(String in) {
		return build(new StringInputStream(in));
	}

	@Override
	public void preproc_event(PreProcEvent event) {
		if (event.type == Type.BeginExpand) {
//			fEventStack.push(event);
			SVPreProcModelNode n = new SVPreProcModelNode(event.text, event.pos);
			
			// Add a new child node
			fModelStack.push(n);
		} else if (event.type == Type.EndExpand) {
			SVPreProcModelNode n = fModelStack.pop();
			n.setEnd(event.pos);
			if (fModelStack.size() > 0) {
				fModelStack.peek().add(n);
			} else {
				fRoot = n;
			}
//			PreProcEvent ev = fEventStack.pop();
//			fExtents.add(new Tuple<Integer, Integer>(ev.pos, event.pos));
		}
	}

}
