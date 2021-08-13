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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.console.ConsoleColorProvider;
import org.eclipse.debug.ui.console.IConsoleColorProvider;
import org.eclipse.debug.ui.console.IConsoleLineTracker;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;

import com.ibm.icu.text.MessageFormat;

public class SVConsoleManager {
	private static SVConsoleManager			fDefault;
	
	private Map<Process, SVConsole>			fActiveConsoles;
	private Map<String, SVGlobalConsole>	fGlobalConsoles;
	
    /**
     * Console document content provider extensions, keyed by extension id
     */
	private Map<String, IConfigurationElement> fColorProviders;
	
    /**
     * Console line trackers; keyed by process type to list of trackers (1:N) 
     */
	private Map<String, List<IConfigurationElement>> fLineTrackers;
	
	/**
	 * Lock for fLineTrackers
	 */
	private Object fLineTrackersLock = new Object();
    
    /**
     * The default color provider. Used if no color provider is contributed
     * for the given process type.
     */
    private IConsoleColorProvider fDefaultColorProvider;	
    
    public SVConsoleManager() {
    	fActiveConsoles = new HashMap<Process, SVConsole>();
    	fGlobalConsoles = new HashMap<String, SVGlobalConsole>();
    }
    
    public static SVConsoleManager getDefault() {
    	if (fDefault == null) {
    		fDefault = new SVConsoleManager();
    	}
    	
    	return fDefault;
    }

    public IConsoleColorProvider getColorProvider(String type) {
        if (fColorProviders == null) {
			fColorProviders = new HashMap<String, IConfigurationElement>();
            IExtensionPoint extensionPoint= Platform.getExtensionRegistry().getExtensionPoint(DebugUIPlugin.getUniqueIdentifier(), IDebugUIConstants.EXTENSION_POINT_CONSOLE_COLOR_PROVIDERS);
            IConfigurationElement[] elements = extensionPoint.getConfigurationElements();
            for (int i = 0; i < elements.length; i++) {
                IConfigurationElement extension = elements[i];
                fColorProviders.put(extension.getAttribute("processType"), extension); //$NON-NLS-1$
            }
        }
        IConfigurationElement extension = fColorProviders.get(type);
        if (extension != null) {
            try {
                Object colorProvider = extension.createExecutableExtension("class"); //$NON-NLS-1$
                if (colorProvider instanceof IConsoleColorProvider) {
                    return (IConsoleColorProvider)colorProvider;
                } 
                DebugUIPlugin.logErrorMessage(MessageFormat.format(
                		"Extension {0} must specify an instanceof IConsoleColorProvider for class attribute.", //$NON-NLS-1$
						new Object[] { extension.getDeclaringExtension().getUniqueIdentifier() }));
            } catch (CoreException e) {
                DebugUIPlugin.log(e);
            }
        }
        //no color provider found of specified type, return default color provider.
        if (fDefaultColorProvider == null) {
            fDefaultColorProvider = new ConsoleColorProvider();
        }
        return fDefaultColorProvider;
    } 

    /**
     * Returns the Line Trackers for a given process type.
     * @param process The process for which line trackers are required.
     * @return An array of line trackers which match the given process type.
     */
    public IConsoleLineTracker[] getLineTrackers(String type) {
        
        if (fLineTrackers == null) {
			synchronized (fLineTrackersLock) { // can't use fLineTrackers as lock as it is null here
				fLineTrackers = new HashMap<String, List<IConfigurationElement>>();
				IExtensionPoint extensionPoint = Platform.getExtensionRegistry().getExtensionPoint(DebugUIPlugin.getUniqueIdentifier(), IDebugUIConstants.EXTENSION_POINT_CONSOLE_LINE_TRACKERS);
				IConfigurationElement[] elements = extensionPoint.getConfigurationElements();
				for (int i = 0; i < elements.length; i++) {
					IConfigurationElement extension = elements[i];
					String processType = extension.getAttribute("processType"); //$NON-NLS-1$
					List<IConfigurationElement> list = fLineTrackers.get(processType);
					if (list == null) {
						list = new ArrayList<IConfigurationElement>();
						fLineTrackers.put(processType, list);
					}
					list.add(extension);
				}
			}
        }
        
		ArrayList<IConsoleLineTracker> trackers = new ArrayList<IConsoleLineTracker>();
        if (type != null) {
			List<IConfigurationElement> lineTrackerExtensions;
			synchronized (fLineTrackers) {// need to synchronize as the update to list might be still happening
				lineTrackerExtensions = fLineTrackers.get(type);
			}
            if(lineTrackerExtensions != null) {   
				for (IConfigurationElement element : lineTrackerExtensions) {
					try {
						trackers.add((IConsoleLineTracker) element.createExecutableExtension("class")); //$NON-NLS-1$
                    } catch (CoreException e) {
                        DebugUIPlugin.log(e);
                    }
				}
            }
        }
        return trackers.toArray(new IConsoleLineTracker[0]);
    }
    
    public SVGlobalConsole openConsole(
    		String			name,
    		String			type) {
    	if (!fGlobalConsoles.containsKey(name)) {
    		SVGlobalConsole c = new SVGlobalConsole(this, name, type, null);
    		fGlobalConsoles.put(name, c);
    		
    		IConsoleManager mgr = ConsolePlugin.getDefault().getConsoleManager();
    		mgr.addConsoles(new org.eclipse.ui.console.IConsole[] {c});
    	}
    	return fGlobalConsoles.get(name);
    }

    public SVProcessConsole openProcessConsole(
    		IProcess 			process,
    		ImageDescriptor		img) {
    	SVProcessConsole ret = null;

    	// Find and remove any existing console with the same name
    	String name = process.getLabel();
    	
    	IConsoleManager mgr = ConsolePlugin.getDefault().getConsoleManager();
    	for (int i=0; i<mgr.getConsoles().length; i++) {
    		org.eclipse.ui.console.IConsole c = mgr.getConsoles()[i];
    		
    		if (c.getName().equals(name)) {
    			mgr.removeConsoles(new org.eclipse.ui.console.IConsole[]{c});
    			i--;
    		}
    	}
    	
    	// Check whether the Console view if visible
    	Display.getDefault().asyncExec(new Runnable() {
    		public void run() {
    		IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    		IViewPart c_view = page.findView(IConsoleConstants.ID_CONSOLE_VIEW);

    		if (c_view == null) {
    			try {
    				page.showView(IConsoleConstants.ID_CONSOLE_VIEW);
    			} catch (PartInitException e) {
    				e.printStackTrace();
    			}
    		}
    		}
    	});
    	
    	
   		ret = new SVProcessConsole(this, process, img);
   		mgr.addConsoles(new org.eclipse.ui.console.IConsole[] {ret});
   		
    	return ret;
    }
}
