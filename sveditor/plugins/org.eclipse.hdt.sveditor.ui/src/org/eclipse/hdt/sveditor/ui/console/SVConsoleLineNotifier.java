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
package org.eclipse.hdt.sveditor.ui.console;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.Preferences.IPropertyChangeListener;
import org.eclipse.core.runtime.Preferences.PropertyChangeEvent;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.ui.console.IConsoleLineTracker;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IPatternMatchListener;
import org.eclipse.ui.console.PatternMatchEvent;
import org.eclipse.ui.console.TextConsole;

public class SVConsoleLineNotifier implements IPatternMatchListener, IPropertyChangeListener {

	private List<IConsoleLineTracker> fListeners = new ArrayList<IConsoleLineTracker>(2);
	private IConsoleLineTracker			fTrackers[];

	private SVConsole			fConsole = null;
	
	public SVConsoleLineNotifier(IConsoleLineTracker trackers[]) {
		fTrackers = trackers;
	}

	@Override
	public void connect(TextConsole console) {
		
		if (console instanceof IOConsole) {
			fConsole = (SVConsole)console;
			
			for (int i = 0; i < fTrackers.length; i++) {
				fTrackers[i].init(fConsole);
		        if (!fListeners.contains(fTrackers[i])) {
					fListeners.add(fTrackers[i]);
				}				
			}
        
//			fConsole.addPropertyChangeListener(this);		
		}
	}

	@Override
	public void disconnect() {
        try {
            IDocument document = fConsole.getDocument();
            if (document != null) {
                int lastLine = document.getNumberOfLines() - 1;
                if (document.getLineDelimiter(lastLine) == null) {
                    IRegion lineInformation = document.getLineInformation(lastLine);
                    lineAppended(lineInformation);
                }
            }
        } catch (BadLocationException e) {
        }		
	}

	@Override
	public void matchFound(PatternMatchEvent event) {
        try  {
            IDocument document = fConsole.getDocument();
            int lineOfOffset = document.getLineOfOffset(event.getOffset());
            String delimiter = document.getLineDelimiter(lineOfOffset);
            int strip = delimiter==null ? 0 : delimiter.length();
            Region region = new Region(event.getOffset(), event.getLength()-strip); 
            lineAppended(region);
        } catch (BadLocationException e) {}		
	}

    public void lineAppended(IRegion region) {
        int size = fListeners.size();
        for (int i=0; i<size; i++) {
            IConsoleLineTracker tracker = fListeners.get(i);
            tracker.lineAppended(region);
        }
    }
    
	@Override
	public void propertyChange(PropertyChangeEvent event) {
		// TODO Auto-generated method stub

	}

	@Override
	public String getPattern() {
        return ".*\\r(\\n?)|.*\\n"; //$NON-NLS-1$
	}

	@Override
	public int getCompilerFlags() {
		return 0;
	}

	@Override
	public String getLineQualifier() {
        return "\\n|\\r"; //$NON-NLS-1$
	}

}
