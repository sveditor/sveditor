/*******************************************************************************
 * Copyright (c) 2000, 2012 IBM Corporation and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Armond Paiva - repurposed from JDT for use in SVEditor
 *******************************************************************************/
package org.eclipse.hdt.sveditor.ui.text.hover;

import org.eclipse.osgi.util.NLS;


/**
 * Helper class to get NLSed messages.
 */
final class SVHoverMessages extends NLS {

	private static final String BUNDLE_NAME= SVHoverMessages.class.getName();

	private SVHoverMessages() {
		// Do not instantiate
	}

	public static String AbstractAnnotationHover_action_configureAnnotationPreferences;
	public static String AbstractAnnotationHover_message_singleQuickFix;
	public static String AbstractAnnotationHover_message_multipleQuickFix;
	public static String AbstractAnnotationHover_multifix_variable_description;

	public static String JavadocHover_back;
	public static String JavadocHover_back_toElement_toolTip;
	public static String JavadocHover_noAttachments;
	public static String JavadocHover_noAttachedJavadoc;
	public static String JavadocHover_noAttachedSource;
	public static String JavadocHover_noInformation;
	public static String JavadocHover_constantValue_hexValue;
	public static String JavadocHover_error_gettingJavadoc;
	public static String JavadocHover_forward;
	public static String JavadocHover_forward_toElement_toolTip;
	public static String JavadocHover_forward_toolTip;
	public static String JavadocHover_openDeclaration;
	public static String JavadocHover_showInJavadoc;
	public static String JavaSourceHover_skippedLines;

	public static String JavaTextHover_createTextHover;

	public static String NoBreakpointAnnotation_addBreakpoint;

	public static String NLSStringHover_NLSStringHover_missingKeyWarning;
	public static String NLSStringHover_NLSStringHover_PropertiesFileCouldNotBeReadWarning;
	public static String NLSStringHover_NLSStringHover_PropertiesFileNotDetectedWarning;
	public static String NLSStringHover_open_in_properties_file;
	public static String ProblemHover_action_configureProblemSeverity;

	public static String ProblemHover_chooseSettingsTypeDialog_button_cancel;
	public static String ProblemHover_chooseSettingsTypeDialog_button_project;
	public static String ProblemHover_chooseSettingsTypeDialog_button_workspace;
	public static String ProblemHover_chooseSettingsTypeDialog_checkBox_dontShowAgain;
	public static String ProblemHover_chooseSettingsTypeDialog_message;
	public static String ProblemHover_chooseSettingsTypeDialog_title;

	static {
		NLS.initializeMessages(BUNDLE_NAME, SVHoverMessages.class);
	}
}
