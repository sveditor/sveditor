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


package net.sf.sveditor.ui.editor.actions;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.scanutils.IRandomAccessTextScanner;
import net.sf.sveditor.core.srcgen.MethodGenerator;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.ISVEditor;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;

public class OverrideTaskFuncImpl {
	private ISVEditor						fEditor;
	private IOverrideMethodsTargetProvider	fTargetProvider;
	
	public OverrideTaskFuncImpl(
			ISVEditor editor,
			IOverrideMethodsTargetProvider	target_provider) {
		fEditor 		= editor;
		fTargetProvider = target_provider;
	}
	
	public void run() {
		IDocument doc = fEditor.getDocument();
		ITextSelection sel = fEditor.getTextSel();
		
		int offset = sel.getOffset() + sel.getLength();

		// Now, iterate through the items in the file and find something
		// with the same name
		SVDBFile file = fEditor.getSVDBFile();

		ISVDBScopeItem active_scope = SVDBSearchUtils.findActiveScope(
				file, fEditor.getTextSel().getStartLine());
		
		ISVDBScopeItem insert_point = active_scope;
		
		// Make the default insert point the current cursor location
		int insert_point_line = fEditor.getTextSel().getStartLine();
		
		if (insert_point.getType() != SVDBItemType.Class) {
			
			
			// If the active scope isn't a class, try to make it a class..
			
			while (insert_point != null && 
					insert_point.getType() != SVDBItemType.Class &&
					insert_point.getParent() != null &&
					insert_point.getParent().getType() != SVDBItemType.Class) {
				insert_point = insert_point.getParent();
			}
			
			if (insert_point.getParent() != null && 
					insert_point.getParent().getType() == SVDBItemType.Class) {
				// insert the new code after the element
				insert_point_line = insert_point.getEndLocation().getLine();
			} else {
				// Odd... Not quite sure what to do here
				System.out.println("[ERROR] problem finding correct insert point");
				return;
			}
		}

		while (active_scope != null && 
				active_scope.getType() != SVDBItemType.Class) {
			active_scope = active_scope.getParent();
		}
		
		if (active_scope == null) {
			return;
		}
		
		List<SVDBTaskFuncScope> targets = fTargetProvider.getTargets(active_scope);
		
		if (targets == null) {
			return;
		}

		// Now, insert new code at the insertion point
		
		try {
			StringBuilder new_tf = new StringBuilder();
			MethodGenerator gen = new MethodGenerator();
			
			// Add a little white-space at the top
			new_tf.append("\n\n");
			
			for (SVDBTaskFuncScope tf : targets) {
				new_tf.append(gen.generate(tf));
			}
			
			offset = doc.getLineOffset(insert_point_line);
			doc.replace(offset, 0, new_tf.toString());
			
			// Now, format the new addition if auto-indent is enabled
			boolean indent_en = SVUiPlugin.getDefault().getPreferenceStore().getBoolean(
					SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S);
			
			if (indent_en) {
				int line_cnt = 0;
				
				for (int i=0; i<new_tf.length(); i++) {
					if (new_tf.charAt(i) == '\n') {
						line_cnt++;
					}
				}
				// re-partition document
				doc.computePartitioning(0, doc.getLength());
				IRandomAccessTextScanner text_scanner =  new SVDocumentTextScanner(doc, 0);
				
				ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
				SVIndentScanner scanner = new SVIndentScanner(text_scanner);
				
				indenter.init(scanner);
				
				try {
					String str = indenter.indent(insert_point_line+1, 
							(insert_point_line+line_cnt));
					doc.replace(offset, new_tf.length(), str);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}

}
