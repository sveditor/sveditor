package net.sf.sveditor.ui.editor.actions;

import java.util.Iterator;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;

public class FoldActionToggle extends AbstractHandler implements IHandler {

	@SuppressWarnings("unchecked")
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		SVEditor sve = SVUiPlugin.getActiveSVEditor();
		
		if (sve != null) {
			ProjectionAnnotationModel pm = sve.getProjectionAnnotationModel();
			ITextSelection tsel = sve.getTextSel();
			
			if (tsel != null) {
				Iterator<Object> it = (Iterator<Object>)pm.getAnnotationIterator(tsel.getOffset(), tsel.getLength(), true, true);
				while (it.hasNext()) {
					ProjectionAnnotation ann = (ProjectionAnnotation)it.next();
					if (ann.isCollapsed()) {
						pm.expand(ann);
					} else {
						pm.collapse(ann);
					}
				}
			}
		}		
		
		return null;
	}

}
