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

public class FoldActionExpand extends AbstractHandler implements IHandler {

	@SuppressWarnings("rawtypes")
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		SVEditor sve = SVUiPlugin.getActiveSVEditor();
		
		if (sve != null) {
			ProjectionAnnotationModel pm = sve.getProjectionAnnotationModel();
			ITextSelection tsel = sve.getTextSel();
			
			if (tsel != null) {
				Iterator it = null;
				// Try a couple of offsets in case we're just outside a fold region
				int offset = tsel.getOffset();
				for (int i=0; i<2; i++) {
					it = pm.getAnnotationIterator(offset, tsel.getLength(), true, true);
					if (it.hasNext()) {
						break;
					}
					offset++;
				}
				while (it.hasNext()) {
					ProjectionAnnotation ann = (ProjectionAnnotation)it.next();
					pm.expand(ann);
				}
			}
		}		
	
		return null;
	}

}
