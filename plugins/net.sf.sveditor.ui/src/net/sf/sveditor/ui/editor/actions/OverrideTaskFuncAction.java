package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.utils.SVDBIndexSearcher;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OverrideTaskFuncAction extends TextEditorAction { 
	
	private SVEditor						fEditor;
	
	
	public OverrideTaskFuncAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fEditor = editor;
		update();
	}
	
	@Override
	public void update() {
		super.update();
	}

	@Override
	public void run() {
		super.run();
		
		IDocument doc = fEditor.getDocumentProvider().getDocument(
				fEditor.getEditorInput());
		ITextSelection sel = getTextSel();
		
		int offset = sel.getOffset() + sel.getLength();

		SVDBIndexSearcher searcher = new SVDBIndexSearcher();
		
		// Add the live version of the file to the search
		searcher.addFile(fEditor.getSVDBFile());
		searcher.addIndex(fEditor.getIndex());
		
		// Now, iterate through the items in the file and find something
		// with the same name
		SVDBFile file = fEditor.getSVDBFile();
		
		SVDBScopeItem active_scope = SVDBSearchUtils.findActiveScope(
				file, getTextSel().getStartLine());
		
		SVDBScopeItem insert_point = active_scope;
		
		System.out.println("active_scope=" + active_scope);

		// Make the default insert point the current cursor location
		int insert_point_line = getTextSel().getStartLine();
		
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

		OverrideMethodsDialog dlg = new OverrideMethodsDialog(
				fEditor.getSite().getShell(), 
				(SVDBModIfcClassDecl)active_scope, searcher);

		System.out.println("open dialog");
		dlg.setBlockOnOpen(true);
		
		dlg.open();
		
		if (dlg.getResult() == null) {
			return;
		}
		
		// Now, insert new code at the insertion point
		
		try {
			StringBuilder new_tf = new StringBuilder();
			
			// Add a little white-space at the top
			new_tf.append("\n\n");
			
			for (Object obj : dlg.getResult()) {
				if (obj instanceof SVDBTaskFuncScope) {
					SVDBTaskFuncScope tf = (SVDBTaskFuncScope)obj;
					
					if (tf.getType() == SVDBItemType.Function) {
						new_tf.append("    function ");
						new_tf.append(tf.getReturnType());
						new_tf.append(" ");
					} else {
						new_tf.append("    task ");
					}
					
					new_tf.append(tf.getName());
					new_tf.append("(");
					
					for (int i=0; i<tf.getParams().size(); i++) {
						SVDBTaskFuncParam p = tf.getParams().get(i);
						
						new_tf.append(p.getTypeName());
						new_tf.append(" ");
						new_tf.append(p.getName());
						
						if (i+1 < tf.getParams().size()) {
							new_tf.append(", ");
						}
					}
					
					new_tf.append(");\n");
					
					new_tf.append("\n");
					
					if (tf.getType() == SVDBItemType.Function) {
						new_tf.append("    endfunction\n");
					} else {
						new_tf.append("    endtask\n");
					}
					
					new_tf.append("\n");
				}
			}
			
			offset = doc.getLineOffset(insert_point_line);
			doc.replace(offset, 0, new_tf.toString());
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}

	private ITextSelection getTextSel() {
		ITextSelection sel = null;
		
		if (getTextEditor() != null) {
			ISelection sel_o = 
				getTextEditor().getSelectionProvider().getSelection();
			if (sel_o != null && sel_o instanceof ITextSelection) {
				sel = (ITextSelection)sel_o;
			} 
		}
		
		return sel;
	}

}
