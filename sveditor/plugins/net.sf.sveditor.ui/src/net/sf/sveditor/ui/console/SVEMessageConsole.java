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
package net.sf.sveditor.ui.console;

import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.internal.ui.preferences.IDebugPreferenceConstants;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

public class SVEMessageConsole extends MessageConsole 
	implements IPropertyChangeListener  {
	
	private MessageConsoleStream			fStdout;
	private MessageConsoleStream			fStderr;
	
	public SVEMessageConsole(String name) {
		super(name, null);
		initConsole();
	}
	
	private void initConsole() {
        IPreferenceStore store = DebugUIPlugin.getDefault().getPreferenceStore();
        store.addPropertyChangeListener(this);
        JFaceResources.getFontRegistry().addListener(this);

		fStdout = newMessageStream();
		fStderr = newMessageStream();
		
		updateConsoleWrap();
		updateTabWidth();
		updateConsoleLimits();
		
		Display.getDefault().asyncExec(new Runnable() {
			@Override
			public void run() {
				updateStreamColors();
				updateConsoleFontColor();
			}
		});
	}

	@Override
	protected void dispose() {
        IPreferenceStore store = DebugUIPlugin.getDefault().getPreferenceStore();
		super.dispose();

		store.removePropertyChangeListener(this);
		JFaceResources.getFontRegistry().removeListener(this);
	}
	
	private void updateStreamColors() {
		fStdout.setColor(DebugUIPlugin.getPreferenceColor(IDebugPreferenceConstants.CONSOLE_SYS_OUT_COLOR));
		fStderr.setColor(DebugUIPlugin.getPreferenceColor(IDebugPreferenceConstants.CONSOLE_SYS_ERR_COLOR));
	}
	
	private void updateConsoleFontColor() {
		setFont(JFaceResources.getFont(IDebugUIConstants.PREF_CONSOLE_FONT));
		setBackground(DebugUIPlugin.getPreferenceColor(IDebugPreferenceConstants.CONSOLE_BAKGROUND_COLOR));
	}
	
	private void updateConsoleWrap() {
		IPreferenceStore store = DebugUIPlugin.getDefault().getPreferenceStore();
		if (store.getBoolean(IDebugPreferenceConstants.CONSOLE_WRAP)) {
			setConsoleWidth(store.getInt(IDebugPreferenceConstants.CONSOLE_WIDTH));
		} else {
			setConsoleWidth(0);
		}
	}
	
	private void updateTabWidth() {
		IPreferenceStore store = DebugUIPlugin.getDefault().getPreferenceStore();
		setTabWidth(store.getInt(IDebugPreferenceConstants.CONSOLE_TAB_WIDTH));
	}
	
	private void updateConsoleLimits() {
		IPreferenceStore store = DebugUIPlugin.getDefault().getPreferenceStore();
		if (store.getBoolean(IDebugPreferenceConstants.CONSOLE_LIMIT_CONSOLE_OUTPUT)) {
			int highWater = store.getInt(IDebugPreferenceConstants.CONSOLE_HIGH_WATER_MARK);
			int lowWater = store.getInt(IDebugPreferenceConstants.CONSOLE_LOW_WATER_MARK);
			setWaterMarks(lowWater, highWater);
		} else {
			setWaterMarks(-1, -1);
		}
	}
	
	public MessageConsoleStream getStdout() { 
		return fStdout;
	}
	
	public MessageConsoleStream getStderr() {
		return fStderr;
	}

	@Override
	public void propertyChange(PropertyChangeEvent event) {
		String property = event.getProperty();
		if (property.equals(IDebugPreferenceConstants.CONSOLE_SYS_OUT_COLOR) ||
				property.equals(IDebugPreferenceConstants.CONSOLE_SYS_ERR_COLOR)) {
			updateStreamColors();
		}
		
		if (property.equals(IDebugUIConstants.PREF_CONSOLE_FONT) ||
				property.equals(IDebugPreferenceConstants.CONSOLE_BAKGROUND_COLOR)) {
			updateConsoleFontColor();
		}
		
		if (property.equals(IDebugPreferenceConstants.CONSOLE_WRAP) ||
				property.equals(IDebugPreferenceConstants.CONSOLE_WIDTH)) {
			updateConsoleWrap();
		}

		if (property.equals(IDebugPreferenceConstants.CONSOLE_TAB_WIDTH)) {
			updateTabWidth();
		}
		
		if (property.equals(IDebugPreferenceConstants.CONSOLE_LIMIT_CONSOLE_OUTPUT) ||
				property.equals(IDebugPreferenceConstants.CONSOLE_HIGH_WATER_MARK) ||
				property.equals(IDebugPreferenceConstants.CONSOLE_LOW_WATER_MARK)) {
			updateConsoleLimits();
		}
	}
	
	public static SVEMessageConsole getConsole(String name) {
		IConsoleManager mgr = ConsolePlugin.getDefault().getConsoleManager();
		SVEMessageConsole ret = null;
		
		for (IConsole c : mgr.getConsoles()) {
			if (c.getName().equals(name) && c instanceof SVEMessageConsole) {
				ret = (SVEMessageConsole)c;
				break;
			}
		}
		
		
		if (ret == null) {
			ret = new SVEMessageConsole(name);
			mgr.addConsoles(new IConsole[] {ret});
		}
		
		return ret;
	}
	
}
