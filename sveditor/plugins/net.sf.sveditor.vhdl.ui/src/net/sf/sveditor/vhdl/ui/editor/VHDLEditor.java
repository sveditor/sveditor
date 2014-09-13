package net.sf.sveditor.vhdl.ui.editor;
import java.util.ResourceBundle;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVCharacterPairMatcher;
import net.sf.sveditor.vhdl.ui.VhdlUiPlugin;
import net.sf.sveditor.vhdl.ui.editor.actions.AddBlockCommentAction;
import net.sf.sveditor.vhdl.ui.editor.actions.RemoveBlockCommentAction;

import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.source.ISourceViewerExtension2;
import org.eclipse.jface.text.source.MatchingCharacterPainter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.editors.text.TextEditor;


public class VHDLEditor extends TextEditor {
	private VHDLCodeScanner				fCodeScanner;
	private SVCharacterPairMatcher		fCharacterMatcher;
	private MatchingCharacterPainter	fMatchingCharacterPainter;

	public VHDLEditor() {
		fCharacterMatcher = new SVCharacterPairMatcher(new char[] {
				'(', ')',
				'[', ']',
				'{', '}'
		},
		VHDLDocumentPartitions.VHD_PARTITIONING,
		new String[] {VHDLDocumentPartitions.VHD_COMMENT});
	}

	@Override
	public void createPartControl(Composite parent) {
		setSourceViewerConfiguration(new VHDLSourceViewerConfig(this));
		
		super.createPartControl(parent);
		
		if (fMatchingCharacterPainter == null) {
			if (getSourceViewer() instanceof ISourceViewerExtension2) {
				fMatchingCharacterPainter = new MatchingCharacterPainter(
						getSourceViewer(), fCharacterMatcher);
				Display display = Display.getCurrent();
				
				// TODO: reference preference store
				fMatchingCharacterPainter.setColor(display.getSystemColor(SWT.COLOR_GRAY));
				((ITextViewerExtension2)getSourceViewer()).addPainter(
						fMatchingCharacterPainter);
			}		
		}
	}
	
	public VHDLCodeScanner getCodeScanner() {
		if (fCodeScanner == null) {
			fCodeScanner = new VHDLCodeScanner(this);
		}
		return fCodeScanner;
	}


	@Override
	public void dispose() {
		// TODO Auto-generated method stub
		super.dispose();
		
		if (fCharacterMatcher != null) {
			fCharacterMatcher.dispose();
		}
	}

	@Override
	protected void initializeKeyBindingScopes() {
		setKeyBindingScopes(new String[] {VhdlUiPlugin.PLUGIN_ID + ".vhdlEditorContext"});
	}

	@Override
	protected void createActions() {
		ResourceBundle bundle = VhdlUiPlugin.getDefault().getResources();
		
		// TODO Auto-generated method stub
		super.createActions();
		
		AddBlockCommentAction add_block_comment = new AddBlockCommentAction(
				bundle, "AddBlockComment.", this);
		add_block_comment.setActionDefinitionId(VhdlUiPlugin.PLUGIN_ID + ".AddBlockComment");
		add_block_comment.setEnabled(true);
		setAction(VhdlUiPlugin.PLUGIN_ID + ".AddBlockComment", add_block_comment);
		
		RemoveBlockCommentAction remove_block_comment = new RemoveBlockCommentAction(
				bundle, "RemoveBlockComment.", this);
		remove_block_comment.setActionDefinitionId(VhdlUiPlugin.PLUGIN_ID + ".RemoveBlockComment");
		remove_block_comment.setEnabled(true);
		setAction(SVUiPlugin.PLUGIN_ID + ".svRemoveBlockCommentAction", remove_block_comment);
	}
	
	

}
