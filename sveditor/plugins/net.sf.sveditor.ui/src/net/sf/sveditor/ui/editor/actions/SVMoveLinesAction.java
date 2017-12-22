package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.swt.widgets.Event;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.MoveLinesAction;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.indent.ISVIndenter;
import net.sf.sveditor.core.indent.SVIndentScanner;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;

public class SVMoveLinesAction extends MoveLinesAction implements IDocumentListener {
	private ITextViewer fTextViewer;
	private boolean 	fUpwards;
	private int			fReferenceLine;			// Line which we are getting WS from
	private int			fStartLine;
	private int			fEndLine;
	private boolean		fChanging = false;
	private int			fSelOffset;
	private int			fSelLength;
	private LogHandle	fLog;

	public SVMoveLinesAction(
			ResourceBundle 	bundle, 
			String 			prefix, 
			ITextEditor 	editor, 
			ITextViewer 	textViewer, 
			boolean 		upwards, 
			boolean 		copy) {
		super(bundle, prefix, editor, textViewer, upwards, copy);
		fLog = LogFactory.getLogHandle("SVMoveLinesAction");
		fTextViewer = textViewer;
		fUpwards = upwards;
	}

	@Override
	public void runWithEvent(Event event) {
		ITextSelection sel = (ITextSelection)fTextViewer.getSelectionProvider().getSelection();
		IDocument doc = fTextViewer.getDocument();

		try {
			fSelOffset = sel.getOffset();
			fSelLength = sel.getLength();
			fStartLine = doc.getLineOfOffset(fSelOffset);
			fEndLine   = doc.getLineOfOffset(fSelOffset+fSelLength);
			if (fUpwards)  {
				fReferenceLine = fStartLine-2;
			}
			else  {
				fReferenceLine = fStartLine-1;
			}
			if (fReferenceLine < 0)  {
				fReferenceLine = 0;			// Default to first line in file
			}
			// If our cursor is at the start of a new line, don't include that line
			// in the lines to be moved
			if ((fSelLength > 0) && (fEndLine > doc.getLineOfOffset(fSelOffset+fSelLength-1)))  {
				fEndLine = doc.getLineOfOffset(fSelOffset+fSelLength-1);
			}
		} catch (BadLocationException e) {
			// Something went wrong...
			fStartLine = -1;
			fEndLine = -1;
		}
		fLog.debug("Start Line: " + (fStartLine) + " End Line: " + (fEndLine) + " Reference Line: " + (fReferenceLine) + " fSeloffset: " + (fSelOffset) + " fSelLength: " + fSelLength );

		if (fTextViewer.getDocument() != null) {
			fTextViewer.getDocument().addDocumentListener(this);
		}
		try {
			super.runWithEvent(event);
			fTextViewer.setSelectedRange(fSelOffset, fSelLength);
			fTextViewer.revealRange(fSelOffset, fSelLength);
		} finally {
			if (fTextViewer.getDocument() != null) {
				fTextViewer.getDocument().removeDocumentListener(this);
			}
		}
	}

	@Override
	public void documentAboutToBeChanged(DocumentEvent event) { }

	@Override
	public void documentChanged(DocumentEvent event) {

		// NOP if this event was triggered by a change below
		// or if we failed to identify the start/end line
		// or if we are moving up, from line 0
		if (fChanging || (fStartLine < 0) || (fStartLine == 0 && fUpwards) || fEndLine == -1) {
			return;
		}

		// Tweak start/end line to match the direction of move
		if (fUpwards) {
			fStartLine--;
			fEndLine--;
		} else {
			fStartLine++;
			fEndLine++;
		}
		IDocument doc = fTextViewer.getDocument();
		SVDocumentTextScanner text_scanner =  new SVDocumentTextScanner(doc, 0);

		ISVIndenter indenter = SVCorePlugin.getDefault().createIndenter();
		SVIndentScanner scanner = new SVIndentScanner(text_scanner);

		indenter.init(scanner);

		indenter.setIndentIncr(SVUiPlugin.getDefault().getIndentIncr());

		indenter.setAdaptiveIndent(true);
		indenter.setAdaptiveIndentEnd(fReferenceLine+1);		// +1 because indenter starts counting lines at 1, not 0

		try {
			String str = null;
			int length = 0;
			for (int i=fStartLine; i<=fEndLine; i++) {
				length += doc.getLineLength(i);
			}

			try {
				fLog.debug("Indent Start: " + (fStartLine+1) + " Indent End: " + (fEndLine+1) + " Indent Ref: " + fReferenceLine+1);
				// Note: the indenter line counts are off-by-one from the document
				str = indenter.indent(fStartLine+1, fEndLine+1);
				fChanging = true;
				// Update the line content(s) with the properly-indented version
				doc.replace(doc.getLineOffset(fStartLine), length, str);
				fSelOffset = doc.getLineOffset(fStartLine);
				fSelLength = str.length();

			} catch (Exception e) {
				e.printStackTrace();
			} finally {
				fChanging = false;
			}
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}
}
