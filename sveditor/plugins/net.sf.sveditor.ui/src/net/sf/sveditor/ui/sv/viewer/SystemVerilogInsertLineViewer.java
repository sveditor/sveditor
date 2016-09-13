package net.sf.sveditor.ui.sv.viewer;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

public class SystemVerilogInsertLineViewer {
	private Composite			fControl;
	private int					fLineNo;
	private String				fLine;
	private String				fContent;
	private SystemVerilogViewer	fViewer;
	private Button				fUp;
	private Button				fDown;
	
	public SystemVerilogInsertLineViewer(
			Composite 			parent,
			int					style) {
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout(2, false));
		
		fViewer = new SystemVerilogViewer(c, 
				SWT.V_SCROLL+SWT.H_SCROLL+SWT.READ_ONLY);
		fViewer.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		Composite button_bar = new Composite(c, SWT.NONE);
		button_bar.setLayoutData(new GridData(SWT.RIGHT, SWT.TOP, false, false));
		button_bar.setLayout(new GridLayout());
		
		fUp = new Button(button_bar, SWT.PUSH);
		fUp.setText("Up");
		fUp.setLayoutData(new GridData(SWT.FILL, SWT.TOP, true, false));
		fUp.addSelectionListener(fSelectionListener);
		
		fDown = new Button(button_bar, SWT.PUSH);
		fDown.setText("Down");
		fDown.setLayoutData(new GridData(SWT.FILL, SWT.TOP, true, false));
		fDown.addSelectionListener(fSelectionListener);
		
		fContent = "";
		fControl = c;
	}
	
	public Control getControl() {
		return fControl;
	}
	
	public SystemVerilogViewer getSvViewer() {
		return fViewer;
	}
	
	public void setContent(String content) {
		fContent = content;
		updateDoc();
	}

	// Set the line content, but don't change the insertion point
	public void setLine(String line) {
		fLine = line;
		updateDoc();
	}
	
	public void setLine(String line, int lineno) {
		fLine = line;
		fLineNo = lineno;
		
		updateDoc();
	}
	
	protected void updateDoc() {
		StringBuilder content = new StringBuilder();
		int pos=0;
		int lineno=1;
	
		if (fContent != null) {
		do {
			int eol = fContent.indexOf('\n', pos);
			
			if (fLineNo != -1 && fLineNo+1 == lineno) {
				content.append(fLine);
				content.append('\n');
			}
			
			if (eol < 0) {
				content.append(fContent.substring(pos));
				break;
			} else {
				content.append(fContent.substring(pos, eol+1));
			}
			pos = eol+1;
			lineno++;
		} while (true);
		
		if (fLineNo != -1 && fLineNo == lineno) {
			content.append(fLine);
			content.append('\n');
		}
		}
	
		fViewer.setContent(content.toString());
	}
	
	private SelectionListener fSelectionListener = new SelectionListener() {
		
		@Override
		public void widgetSelected(SelectionEvent e) {
			if (e.widget == fUp) {
				if (fLineNo > 0) {
					fLineNo--;
				}
			} else if (e.widget == fDown) {
				fLineNo++;
			}
			updateDoc();
		}
		
		@Override
		public void widgetDefaultSelected(SelectionEvent e) { }
	};

}
