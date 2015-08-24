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


package net.sf.sveditor.ui;

import net.sf.sveditor.ui.wizards.NewSVClassWizard;
import net.sf.sveditor.ui.wizards.NewSVInterfaceWizard;
import net.sf.sveditor.ui.wizards.NewSVModuleWizard;
import net.sf.sveditor.ui.wizards.NewSVPackageWizard;
import net.sf.sveditor.ui.wizards.project.NewSVEProjectWizard;

import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.navigator.resources.ProjectExplorer;
import org.eclipse.ui.wizards.newresource.BasicNewFileResourceWizard;
import org.eclipse.ui.wizards.newresource.BasicNewFolderResourceWizard;

/**
 * Copy most of this from ResourcePerspective from Eclipse
 *  
 * @author ballance
 *
 */
public class SVPerspectiveFactory implements IPerspectiveFactory {

    /**
     * Defines the initial layout for a perspective.  
     *
     * Implementors of this method may add additional views to a
     * perspective.  The perspective already contains an editor folder
     * with <code>ID = ILayoutFactory.ID_EDITORS</code>.  Add additional views
     * to the perspective in reference to the editor folder.
     *
     * This method is only called when a new perspective is created.  If
     * an old perspective is restored from a persistence file then
     * this method is not called.
     *
     * @param layout the factory used to add views to the perspective
     */
    public void createInitialLayout(IPageLayout layout) {
        defineActions(layout);
        defineLayout(layout);
    }

    /**
     * Defines the initial actions for a page.  
     * @param layout The layout we are filling
     */
    public void defineActions(IPageLayout layout) {
        // Add "new wizards".
        layout.addNewWizardShortcut(BasicNewFolderResourceWizard.WIZARD_ID);
        layout.addNewWizardShortcut(BasicNewFileResourceWizard.WIZARD_ID);
        layout.addNewWizardShortcut(NewSVEProjectWizard.ID);
        layout.addNewWizardShortcut(NewSVClassWizard.ID);
        layout.addNewWizardShortcut(NewSVInterfaceWizard.ID);
        layout.addNewWizardShortcut(NewSVModuleWizard.ID);
        layout.addNewWizardShortcut(NewSVPackageWizard.ID);
        // TODO: This should probably be contributed via an extension point
        layout.addNewWizardShortcut(
        		"net.sf.sveditor.svt.ui.svMethodologyClass");
        
        // Add "show views".
        layout.addShowViewShortcut(ProjectExplorer.VIEW_ID);
        layout.addShowViewShortcut(IPageLayout.ID_BOOKMARKS);
        layout.addShowViewShortcut(IPageLayout.ID_OUTLINE);
        layout.addShowViewShortcut(IPageLayout.ID_PROP_SHEET);
        layout.addShowViewShortcut(IPageLayout.ID_PROBLEM_VIEW);
        layout.addShowViewShortcut(IPageLayout.ID_PROGRESS_VIEW);
        layout.addShowViewShortcut(IPageLayout.ID_TASK_LIST);
        layout.addShowViewShortcut("net.sf.sveditor.ui.designHierarchy");

        layout.addActionSet(IPageLayout.ID_NAVIGATE_ACTION_SET);
        
        // Add launcher shortcut
        layout.addActionSet(IDebugUIConstants.LAUNCH_ACTION_SET);
    }

    /**
     * Defines the initial layout for a page.  
     * @param layout The layout we are filling
     */
    public void defineLayout(IPageLayout layout) {
        // Editors are placed for free.
        String editorArea = layout.getEditorArea();

        // Top left.
        IFolderLayout topLeft = layout.createFolder(
                "topLeft", IPageLayout.LEFT, (float) 0.26, editorArea);//$NON-NLS-1$
        topLeft.addView(ProjectExplorer.VIEW_ID);
        topLeft.addPlaceholder(IPageLayout.ID_BOOKMARKS);

        // Add a placeholder for the old navigator to maintain compatibility
        topLeft.addPlaceholder("org.eclipse.ui.views.ResourceNavigator"); //$NON-NLS-1$

        // Bottom left.
        IFolderLayout bottomLeft = layout.createFolder(
                "bottomLeft", IPageLayout.BOTTOM, (float) 0.50,//$NON-NLS-1$
                "topLeft");//$NON-NLS-1$
        bottomLeft.addView(IPageLayout.ID_OUTLINE);

        // Bottom right.
		IFolderLayout bottomRight = layout.createFolder(
                "bottomRight", IPageLayout.BOTTOM, (float) 0.66,//$NON-NLS-1$
                editorArea);
		
		bottomRight.addView(IPageLayout.ID_TASK_LIST);
		
    }

}
