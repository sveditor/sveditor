package net.sf.sveditor.ui.editor;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.texteditor.ITextEditor;

public interface ISVEditor extends ITextEditor {
	
	ISVDBIndexIterator getIndexIterator();
	
	IDocument getDocument();
	
	ITextSelection getTextSel();
	
	SVDBFile getSVDBFile();

}
