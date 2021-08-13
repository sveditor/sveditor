/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.sveditor.ui.pref;


import java.util.Set;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

public class TemplatePropertyDialog extends Dialog {
	private Text				fParameterId;
	private String				fParameterIdStr;
	private Text				fValue;
	private String				fValueStr;
	private Set<String>			fTakenIds;
	private boolean			fCanModifyId;
	private String				fTitle;
	
	public TemplatePropertyDialog(
			Shell shell, 
			int style, 
			Set<String> taken_ids,
			boolean		modify_id,
			String title
			) {
		super(shell);
		fTakenIds = taken_ids;
		fCanModifyId = modify_id;
		fTitle = title;
	}
	
	public TemplatePropertyDialog(
			Shell shell, 
			int style, 
			Set<String> taken_ids,
			boolean		modify_id) {
		super(shell);
		fTakenIds = taken_ids;
		fCanModifyId = modify_id;
		fTitle = "";
	}
	
	public void configureShell (Shell shell) {
		super.configureShell(shell);
		shell.setText(fTitle);
	}

	@Override
	protected boolean isResizable() {
		return true;
	}

	public void setParameterId(String path) {
		fParameterIdStr = path;
		if (fParameterId != null && !fParameterId.isDisposed()) {
			fParameterId.setText(fParameterIdStr);
		}
	}
	
	public String getParameterId() {
		return fParameterIdStr;
	}
	
	public void setValue(String value) {
		fValueStr = value;
		if (fValue != null && !fValue.isDisposed()) {
			fValue.setText(fValueStr);
		}
	}
	
	public String getValue() {
		// We don't want to keep the '\r' in Windows preference values
		return fValueStr.replaceAll("\r", "");
	}
	
	private void validate() {
		boolean ok = true;
		
		ok &= (!fParameterId.getText().trim().equals(""));
		
		if (getButton(IDialogConstants.OK_ID) != null) {
			getButton(IDialogConstants.OK_ID).setEnabled(ok);
		}
	}
	
	@Override
	protected Control createButtonBar(Composite parent) {
		Control c = super.createButtonBar(parent);
		validate();
		return c;
	}
	
	@Override
	protected Control createContents(Composite parent) {
		Composite c = (Composite)super.createContents(parent);

		GridData gd;
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.heightHint = 480;
		gd.widthHint = 640;
		c.setLayoutData(gd);
		
		c.layout();
		
		Composite da = (Composite)getDialogArea();
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		da.setLayoutData(gd);
		
		return c;
	}

	@Override
	protected Control createDialogArea(Composite parent) {
		Label l;
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(2, false));
		
		GridData gd;
		
		l = new Label(frame, SWT.NONE);
		l.setText("Parameter:");
		fParameterId = new Text(frame, SWT.BORDER);
		gd = new GridData(SWT.FILL, SWT.CENTER, true, false);
		gd.widthHint = 250;
		fParameterId.setLayoutData(gd);
		fParameterId.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fParameterIdStr = fParameterId.getText();
				validate();
			}
		});
		
		if (fParameterIdStr != null) {
			fParameterId.setText(fParameterIdStr);
		}
		
		if (!fCanModifyId) {
			fParameterId.setEditable(false);
			fParameterId.setEnabled(false);
		}
		
		fValue = new Text(frame, SWT.MULTI+SWT.BORDER+SWT.V_SCROLL);
		fValue.setFont(JFaceResources.getTextFont());
		fValue.addModifyListener(new ModifyListener() {
			public void modifyText(ModifyEvent e) {
				fValueStr = fValue.getText();
				validate();
			}
		});
		
		if (fValueStr != null) {
			fValue.setText(fValueStr);
		}
		
		gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.horizontalSpan = 2;
		gd.heightHint = 100;
		fValue.setLayoutData(gd);
		
		return frame;
	}
}
