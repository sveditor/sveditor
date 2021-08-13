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

import java.util.ArrayList;
import java.util.List;

public class SVPreProcModelNode {
	private String							fText;
	private int								fStartPos;
	private int								fEndPos;
	private List<SVPreProcModelNode>		fChildren;
	
	public SVPreProcModelNode(String text, int start) {
		fChildren = new ArrayList<SVPreProcModelNode>();
		fText = text;
		fStartPos = start;
		fEndPos = -1;
	}
	
	public void add(SVPreProcModelNode c) {
		fChildren.add(c);
	}
	
	public int getStart() {
		return fStartPos;
	}
	
	public void setStart(int start) {
		fStartPos = start;
	}
	
	public int getEnd() {
		return fEndPos;
	}
	
	public void setEnd(int end) {
		fEndPos = end;
	}
	
	public String getText() {
		return fText;
	}
	
	public List<SVPreProcModelNode> getChildren() {
		return fChildren;
	}
	
	public String toString(String content) {
		StringBuilder sb = new StringBuilder();
		
		dump("", sb, content, this);
		
		return sb.toString();
	}

	private static void dump(
			String				ind,
			StringBuilder		sb, 
			String				content,
			SVPreProcModelNode	n) {
		sb.append(ind + " Node: " + n.fText + " " + n.fStartPos + ".." + n.fEndPos + "\n");
		if (n.fChildren.size() > 0) {
			SVPreProcModelNode fc = n.fChildren.get(0);
			sb.append(content.substring(n.fStartPos, fc.fStartPos) + "\n");
		} else {
			if (n.fEndPos >= content.length()) {
				System.out.println("endPos=" + n.fEndPos + " length=" + content.length());
			}
			sb.append(content.substring(n.fStartPos, n.fEndPos) + "\n");
		}
		for (SVPreProcModelNode sn : n.fChildren) {
			dump(ind + "    ", sb, content, sn);
		}
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		dump("", sb, this);
		
		return sb.toString();
	}
	
	private static void dump(
			String				ind,
			StringBuilder		sb, 
			SVPreProcModelNode	n) {
		sb.append(ind + " Node: " + n.fText + " " + n.fStartPos + ".." + n.fEndPos + "\n");
		for (SVPreProcModelNode sn : n.fChildren) {
			dump(ind + "    ", sb, sn);
		}
	}
}
