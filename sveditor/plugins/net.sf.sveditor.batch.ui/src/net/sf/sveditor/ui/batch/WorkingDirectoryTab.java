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
package net.sf.sveditor.ui.batch;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.variables.IStringVariableManager;
import org.eclipse.core.variables.VariablesPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.internal.ui.DebugUIMessages;
import org.eclipse.debug.internal.ui.SWTFactory;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.debug.ui.StringVariableSelectionDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ContainerSelectionDialog;

public class WorkingDirectoryTab extends AbstractLaunchConfigurationTab {
	
	// Local directory
	private Button fWorkspaceButton;
	private Button fFileSystemButton;
	private Button fVariablesButton;
	
	//bug 29565 fix
	private Button fUseDefaultDirButton = null;
	private Button fUseOtherDirButton = null;
	private Text fOtherWorkingText = null;
	private Text fWorkingDirText;	
	
	private ILaunchConfiguration			fLaunchConfiguration;
	
	public WorkingDirectoryTab() {
	}
	
	@Override
	public String getName() {
		return "Script";
	}

	@Override
	public void createControl(Composite parent) {
		// TODO Auto-generated method stub
		
		GridData gd = null;

		Font font = parent.getFont();	
		Group group = new Group(parent, SWT.NONE);
		group.setLayout(new GridLayout());
		gd = new GridData(GridData.FILL_HORIZONTAL);
		group.setText("Working Directory");
		group.setLayoutData(gd);
		setControl(group);
		
		//default choice
		Composite comp = SWTFactory.createComposite(group, font, 2, 2, GridData.FILL_BOTH, 0, 0);
		fUseDefaultDirButton = SWTFactory.createRadioButton(comp, DebugUIMessages.WorkingDirectoryBlock_18);
		fUseDefaultDirButton.addSelectionListener(fListener);
		fWorkingDirText = SWTFactory.createSingleText(comp, 1); 
		fWorkingDirText.addModifyListener(fListener);
		fWorkingDirText.setEnabled(false);
		//user enter choice
		fUseOtherDirButton = SWTFactory.createRadioButton(comp, DebugUIMessages.WorkingDirectoryBlock_19);
		fUseOtherDirButton.addSelectionListener(fListener);
		fOtherWorkingText = SWTFactory.createSingleText(comp, 1);
		fOtherWorkingText.addModifyListener(fListener);
		//buttons
		Composite buttonComp = SWTFactory.createComposite(comp, font, 3, 2, GridData.HORIZONTAL_ALIGN_END); 
		GridLayout ld = (GridLayout)buttonComp.getLayout();
		ld.marginHeight = 1;
		ld.marginWidth = 0;
		fWorkspaceButton = createPushButton(buttonComp, DebugUIMessages.WorkingDirectoryBlock_0, null); 
		fWorkspaceButton.addSelectionListener(fListener);
		fFileSystemButton = createPushButton(buttonComp, DebugUIMessages.WorkingDirectoryBlock_1, null); 
		fFileSystemButton.addSelectionListener(fListener);
		fVariablesButton = createPushButton(buttonComp, DebugUIMessages.WorkingDirectoryBlock_17, null); 
		fVariablesButton.addSelectionListener(fListener);
	}

	@Override
	public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void initializeFrom(ILaunchConfiguration configuration) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void performApply(ILaunchConfigurationWorkingCopy configuration) {
		// TODO Auto-generated method stub
		
	}
	
	/**
	 * Show a dialog that lets the user select a working directory
	 */
	private void handleWorkingDirBrowseButtonSelected() {
		DirectoryDialog dialog = new DirectoryDialog(getShell());
		dialog.setMessage(DebugUIMessages.WorkingDirectoryBlock_7); 
		String currentWorkingDir = getWorkingDirectoryText();
		if (!currentWorkingDir.trim().equals("")) { //$NON-NLS-1$
			File path = new File(currentWorkingDir);
			if (path.exists()) {
				dialog.setFilterPath(currentWorkingDir);
			}		
		}
		String selectedDirectory = dialog.open();
		if (selectedDirectory != null) {
			fOtherWorkingText.setText(selectedDirectory);
		}		
	}

	/**
	 * Show a dialog that lets the user select a working directory from 
	 * the workspace
	 */
	private void handleWorkspaceDirBrowseButtonSelected() {
	    IContainer currentContainer= getContainer();
		if (currentContainer == null) {
		    currentContainer = ResourcesPlugin.getWorkspace().getRoot();
		} 
		ContainerSelectionDialog dialog = new ContainerSelectionDialog(getShell(), currentContainer, false,	DebugUIMessages.WorkingDirectoryBlock_4); 
		dialog.showClosedProjects(false);
		dialog.open();
		Object[] results = dialog.getResult();		
		if ((results != null) && (results.length > 0) && (results[0] instanceof IPath)) {
			IPath path = (IPath)results[0];
			String containerName = path.makeRelative().toString();
			setOtherWorkingDirectoryText("${workspace_loc:" + containerName + "}"); //$NON-NLS-1$ //$NON-NLS-2$
		}			
	}
	
	/**
	 * Sets the text of the default working directory.
	 * @param dir the directory to set the widget to
	 */
	protected final void setDefaultWorkingDirectoryText(String dir) {
		if(dir != null) {
			fWorkingDirText.setText(dir);
			fUseDefaultDirButton.setSelection(true);
			handleUseDefaultWorkingDirButtonSelected();
		}
	}
	
	/**
	 * Sets the directory of the other working directory to be used.
	 * @param dir the directory to set the widget to
	 */
	protected final void setOtherWorkingDirectoryText(String dir) {
		if(dir != null) {
			fOtherWorkingText.setText(dir);
			fUseDefaultDirButton.setSelection(false);
			fUseOtherDirButton.setSelection(true);
			handleUseOtherWorkingDirButtonSelected();
		}
	}	
	
	private static URI toURI(IPath uri) {
		try {
			return new URI(uri.toOSString());
		} catch (URISyntaxException e) {
			e.printStackTrace();
			return null;
		}
	}
	
	/**
	 * Returns the selected workspace container or <code>null</code>
	 * @return the selected workspace container or <code>null</code> 
	 */
	protected IContainer getContainer() {
		String path = getWorkingDirectoryText();
		if (path.length() > 0) {
		    IResource res = null;
		    IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		    if (path.startsWith("${workspace_loc:")) { //$NON-NLS-1$
		        IStringVariableManager manager = VariablesPlugin.getDefault().getStringVariableManager();
			    try {
                    path = manager.performStringSubstitution(path, false);
                    IPath uriPath = new Path(path).makeAbsolute();
                    IContainer[] containers = root.findContainersForLocationURI(toURI(uriPath));
                    if (containers.length > 0) {
                        res = containers[0];
                    }
                } 
			    catch (CoreException e) {
			    	log(e);
			    }
			} 
		    else {	    
				res = root.findMember(path);
			}
			if (res instanceof IContainer) {
				return (IContainer)res;
			}
		}
		return null;
	}	
	
	/**
	 * Logs exceptions that have been caught by this working directory block.
	 * Subclasses should reimplement if they wish to monitor such exceptions.
	 * Default implementation does nothing.
	 * @param e the exception to log
	 */
	protected void log(CoreException e) {
		// nothing
	}	
	
	/**
	 * The default working dir radio button has been selected.
	 */
	private void handleUseDefaultWorkingDirButtonSelected() {
		fWorkspaceButton.setEnabled(false);
		fOtherWorkingText.setEnabled(false);
		fVariablesButton.setEnabled(false);
		fFileSystemButton.setEnabled(false);
		fUseOtherDirButton.setSelection(false);
	}

	/**
	 * The other working dir radio button has been selected
	 */
	private void handleUseOtherWorkingDirButtonSelected() {
		fOtherWorkingText.setEnabled(true);
		fWorkspaceButton.setEnabled(true);
		fVariablesButton.setEnabled(true);
		fFileSystemButton.setEnabled(true);
		updateLaunchConfigurationDialog();
	}

	/**
	 * The working dir variables button has been selected
	 */
	private void handleWorkingDirVariablesButtonSelected() {
		StringVariableSelectionDialog dialog = new StringVariableSelectionDialog(getShell());
		dialog.open();
		String variableText = dialog.getVariableExpression();
		if (variableText != null) {
			fOtherWorkingText.insert(variableText);
		}
	}
	
	/**
	 * Retrieves the path from the text box that has been selected.
	 * @return the working directory the user wishes to use
	 */
	protected final String getWorkingDirectoryText() {
		if(fUseDefaultDirButton.getSelection()) {
			return fWorkingDirText.getText().trim();
		}
		return fOtherWorkingText.getText().trim();
	}
	
	/**
	 * Sets the default working directory.
	 */
	protected void setDefaultWorkingDir() {
		try {
			ILaunchConfiguration config = getLaunchConfiguration();
			if (config != null) {
				IProject project = getProject(config);
				if (project != null) {
					setDefaultWorkingDirectoryText("${workspace_loc:" + project.getFullPath().makeRelative().toOSString() + "}");  //$NON-NLS-1$//$NON-NLS-2$
					return;
				}
			}
		} 
		catch (CoreException ce) {
			log(ce);
		}
		setDefaultWorkingDirectoryText(System.getProperty("user.dir")); //$NON-NLS-1$
	}	
	
	/**
	 * Returns the launch configuration that this working directory block is using.
	 * @return this working directory block's launch configuration
	 */
	protected ILaunchConfiguration getLaunchConfiguration() {
		return fLaunchConfiguration;
	}	
	

	protected IProject getProject(ILaunchConfiguration config) throws CoreException {
		return null;
	}
	
	/**
	 * A listener to update for text changes and widget selection
	 */
	private class WidgetListener extends SelectionAdapter implements ModifyListener {
		public void modifyText(ModifyEvent e) {
			scheduleUpdateJob();
		}
		public void widgetSelected(SelectionEvent e) {
			Object source= e.getSource();
			if (source == fWorkspaceButton) {
				handleWorkspaceDirBrowseButtonSelected();
			}
			else if (source == fFileSystemButton) {
				handleWorkingDirBrowseButtonSelected();
			} 
			else if (source == fVariablesButton) {
				handleWorkingDirVariablesButtonSelected();
			} 
			else if(source == fUseDefaultDirButton) {
				//only perform the action if this is the button that was selected
				if(fUseDefaultDirButton.getSelection()) {
					setDefaultWorkingDir();
				}
			} 
			else if(source == fUseOtherDirButton) {
				//only perform the action if this is the button that was selected
				if(fUseOtherDirButton.getSelection()) {
					handleUseOtherWorkingDirButtonSelected();
				}
			}
		}
	}
	
	private WidgetListener				fListener = new WidgetListener();
}
