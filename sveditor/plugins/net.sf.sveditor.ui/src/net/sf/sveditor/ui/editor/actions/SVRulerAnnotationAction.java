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
package net.sf.sveditor.ui.editor.actions;

import java.util.Iterator;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.SVOverrideMethodAnnotation;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.texteditor.SelectMarkerRulerAction;

public class SVRulerAnnotationAction extends SelectMarkerRulerAction {
	private IVerticalRuler				fVertRuler;
	private SVEditor					fEditor;
	
	public SVRulerAnnotationAction(
			ResourceBundle 	bundle, 
			String 			prefix, 
			SVEditor 		editor, 
			IVerticalRuler 	ruler){
		super(bundle, prefix, editor, ruler);
		fVertRuler = ruler;
		fEditor = editor;
	}

	@Override
	@SuppressWarnings("unchecked")
	public void update() {
		final int activeLine = fVertRuler.getLineOfLastMouseButtonActivity();
		IAnnotationModel ann_model = fEditor.getAnnotationModel();

		Iterator<Annotation> ann_it = ann_model.getAnnotationIterator();
		Annotation target_ann = null;
	
		while (ann_it.hasNext()) {
			Annotation ann = ann_it.next();
			Position p = ann_model.getPosition(ann);
			try {
				int line = fEditor.getDocument().getLineOfOffset(p.getOffset());
			
				if (line == activeLine) {
					target_ann = ann;
					break;
				}
			} catch (BadLocationException e) {}
		}
		
		if (target_ann != null) {
			if (target_ann instanceof SVOverrideMethodAnnotation) {
				SVDBTask tf = ((SVOverrideMethodAnnotation)target_ann).getTask();
				try {
					SVEditorUtil.openEditor(tf);
				} catch (PartInitException e) {
					e.printStackTrace();
				}
			}

		}

		setEnabled((target_ann != null));
	}

	@Override
	public void run() {
		super.run();
	}
	
	

}
