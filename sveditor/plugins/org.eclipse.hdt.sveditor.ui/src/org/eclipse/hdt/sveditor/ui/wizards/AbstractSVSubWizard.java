/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.wizards;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.wizard.IWizard;
import org.eclipse.jface.wizard.IWizardPage;

public abstract class AbstractSVSubWizard implements ISVSubWizard {
	protected IWizard							fWizard;
	protected Map<String, Object>				fOptions;
	protected List<IWizardPage>					fWizardPages;

	public AbstractSVSubWizard() {
		fWizardPages = new ArrayList<IWizardPage>();
	}

	public void init(IWizard wizard, Map<String, Object> options) {
		fWizard = wizard;
		fOptions = options;
		addPages();
	}
	
	public abstract void addPages();
	
	public void addPage(IWizardPage page) {
		fWizardPages.add(page);
		page.setWizard(fWizard);
	}
	
	public Map<String, Object> getOptions() {
		return fOptions;
	}

	public IWizardPage getNextPage(IWizardPage page) {
		IWizardPage ret = null;
		
		int idx = fWizardPages.indexOf(page);
		if (idx == -1) {
			ret = fWizardPages.get(0);
		} else {
			if (idx+1 < fWizardPages.size()) {
				ret = fWizardPages.get(idx+1);
			}
		}
		return ret;
	}

	public IWizardPage getPreviousPage(IWizardPage page) {
		int idx = fWizardPages.indexOf(page);
		IWizardPage ret = null;
		
		if (idx > 0) {
			ret = fWizardPages.get(idx-1);
		}
		return ret;
	}

	public boolean canFinish() {
		boolean can_finish = true;
		
		for (IWizardPage p : fWizardPages) {
			if (!p.isPageComplete()) {
				can_finish = false;
			}
		}

		return can_finish;
	}
}
