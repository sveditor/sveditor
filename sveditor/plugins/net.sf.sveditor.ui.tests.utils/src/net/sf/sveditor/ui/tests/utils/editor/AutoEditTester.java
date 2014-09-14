/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.tests.utils.editor;

import java.util.HashMap;
import java.util.Map;

import junit.framework.TestCase;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.swt.widgets.Display;

public class AutoEditTester {
	private Map<String, IAutoEditStrategy> fStrategyMap = new HashMap<String, IAutoEditStrategy>();
	private IDocument 			fDoc;
	private String 				fPartitioning;
	private int 				fCaretOffset;
	private LogHandle			fLog;

	public AutoEditTester(IDocument doc, String partitioning) {
		super();
		fDoc = doc;
		fPartitioning = partitioning;
		fLog = LogFactory.getLogHandle("AutoEditTester");
	}
	
	public IDocument getDocument() {
		return fDoc;
	}

	public void setAutoEditStrategy(String contentType, IAutoEditStrategy aes) {
		fStrategyMap.put(contentType, aes);
	}

	public IAutoEditStrategy getAutoEditStrategy(String contentType) {
		return (IAutoEditStrategy)fStrategyMap.get(contentType);
	}

	/**
	 * Empties the document, and returns the caret to the origin (0,0)
	 */
	public void reset() {
		try {
			goTo(0,0);
			fDoc.set("");
		} catch(BadLocationException ble) {
			TestCase.fail(ble.getMessage());
		}
	}
	
	public void type(String text) throws BadLocationException {
		type(text, -1);
	}
	
	public void type(String text, int pos) throws BadLocationException {
		fLog.debug("--> type \"" + text + "\"");
		for (int i = 0; i < text.length(); ++i) {
			type(text.charAt(i));
		}
		
		if (pos != -1) {
			setCaretOffset(pos);
		}

		for (int i=0; i<10; i++) {
//			fLog.debug("  delay iteration " + i);
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {}
			while (Display.getDefault().readAndDispatch()) {}
		}
		fLog.debug("<-- type ...");
	}

	public void type(char c) throws BadLocationException {
		TestDocumentCommand command = new TestDocumentCommand(fCaretOffset, 0, new String(new char[] { c }));
		customizeDocumentCommand(command);
		fCaretOffset = command.exec(fDoc);
	}

	private void customizeDocumentCommand(TestDocumentCommand command) throws BadLocationException {
		IAutoEditStrategy aes = getAutoEditStrategy(getContentType());
		if (aes != null) {
			aes.customizeDocumentCommand(fDoc, command);
		}
	}

	public void type(int offset, String text) throws BadLocationException {
		fCaretOffset = offset;
		type(text);
	}

	public void type(int offset, char c) throws BadLocationException {
		fCaretOffset = offset;
		type(c);
	}

	public void paste(String text) throws BadLocationException {
		TestDocumentCommand command = new TestDocumentCommand(fCaretOffset, 0, text);
		customizeDocumentCommand(command);
		fCaretOffset = command.exec(fDoc);
	}

	public void paste(int offset, String text) throws BadLocationException {
		fCaretOffset = offset;
		paste(text);
	}

	public void backspace(int n) throws BadLocationException {
		for (int i = 0; i < n; ++i) {
			backspace();
		}
	}
	
	public void backspace() throws BadLocationException {
		TestDocumentCommand command = new TestDocumentCommand(fCaretOffset - 1, 1, ""); //$NON-NLS-1$
		customizeDocumentCommand(command);
		fCaretOffset = command.exec(fDoc);
	}

	public int getCaretOffset() {
		return fCaretOffset;
	}

	public int setCaretOffset(int offset) {
		fCaretOffset = offset;
		if (fCaretOffset < 0)
			fCaretOffset = 0;
		else if (fCaretOffset > fDoc.getLength())
			fCaretOffset = fDoc.getLength();
		return fCaretOffset;
	}
	
	/**
	 * Moves caret right or left by the given number of characters.
	 * 
	 * @param shift Move distance.
	 * @return New caret offset.
	 */
	public int moveCaret(int shift) {
		return setCaretOffset(fCaretOffset + shift);
	}
	
	public int goTo(int line) throws BadLocationException {
		fCaretOffset = fDoc.getLineOffset(line);
		return fCaretOffset;
	}

	public int goTo(int line, int column) throws BadLocationException {
		if (column < 0 || column > fDoc.getLineLength(line)) {
			throw new BadLocationException("No column " + column + " in line " + line); //$NON-NLS-1$ $NON-NLS-2$
		}
		fCaretOffset = fDoc.getLineOffset(line) + column;
		return fCaretOffset;
	}

	public int getCaretLine() throws BadLocationException {
		return fDoc.getLineOfOffset(fCaretOffset);
	}

	public int getCaretColumn() throws BadLocationException {
		IRegion region = fDoc.getLineInformationOfOffset(fCaretOffset);
		return fCaretOffset - region.getOffset();
	}

	public char getChar() throws BadLocationException {
		return getChar(0);
	}
	
	public char getChar(int i) throws BadLocationException {
		return fDoc.getChar(fCaretOffset+i);
	}
	
	public String getLine() throws BadLocationException {
		return getLine(0);
	}
	
	public String readLine() throws BadLocationException {
		IRegion region = fDoc.getLineInformation(getCaretLine());
		String ret = fDoc.get(region.getOffset(), region.getLength());
		fCaretOffset = region.getOffset() + region.getLength()+1;
		return ret; 
	}

	public String getLine(int i) throws BadLocationException {
		IRegion region = fDoc.getLineInformation(getCaretLine() + i);
		return fDoc.get(region.getOffset(), region.getLength());
	}
	
	public void setContent(String content) throws BadLocationException {
		fDoc.set(content);
		fCaretOffset = fDoc.getLength()-1;
	}
	
	public String getContent() throws BadLocationException {
		return fDoc.get();
	}

	public String getContentType() throws BadLocationException {
		return getContentType(0);
	}

	public String getContentType(int i) throws BadLocationException {
		return TextUtilities.getContentType(fDoc, fPartitioning, fCaretOffset + i, false);
	}

}
