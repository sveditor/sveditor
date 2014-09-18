package net.sf.sveditor.vhdl.ui.tests.editor;

import java.io.File;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.vhdl.ui.editor.VHDLEditor;
import net.sf.sveditor.vhdl.ui.tests.VhdlEditorTestCaseBase;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.texteditor.ITextEditor;

public class TestBlockComment extends VhdlEditorTestCaseBase {
	
	public void testBlockComment() throws PartInitException, BadLocationException, ExecutionException, 
		NotDefinedException, NotEnabledException, NotHandledException {
	
		File foo_vhd = new File(fTmpDir, "foo.vhd");
		SVFileUtils.copy(
				"entity foo is\n" +
				"\n" +
				"end entity;\n",
				foo_vhd);
		
		VHDLEditor ved = openEditor(foo_vhd.getAbsolutePath());
		assertNotNull(ved);
		
		IDocument doc = ved.getDocumentProvider().getDocument(ved.getEditorInput());
		fLog.debug("Initial doc:\n" + doc.get());
		
		ISelectionProvider p = ved.getSelectionProvider();
		p.setSelection(new TextSelection(0, doc.getLineOffset(3)));
		
		while (Display.getDefault().readAndDispatch()) {}
		
		IAction action = ved.getAction("net.sf.sveditor.vhdl.ui.AddBlockComment");
		
		action.run();
		
		while (Display.getDefault().readAndDispatch()) {}
		
		fLog.debug("Resulting doc:\n" + doc.get());
		
		assertEquals(
				"--entity foo is\n" +
				"--\n" +
				"--end entity;\n",
				doc.get());
	
		// Ensure that the selection was expanded to cover the newly-comment code
		ITextSelection sel = (ITextSelection)p.getSelection();
		String sel_text = doc.get(sel.getOffset(),  sel.getLength());
		
		assertEquals(
				"--entity foo is\n" +
				"--\n" +
				"--end entity;\n",
				sel_text);
	}

}
