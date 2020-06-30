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
package org.eclipse.hdt.sveditor.core.tagproc;


public class DefaultTemplateParameterProvider extends TemplateParameterProvider {
	
	public static final String				FILE_HEADER = "file_header";
	public static final String				FILE_HEADER_DFLT =
			"/****************************************************************************\n" +
			" * ${filename}\n" +
			" ****************************************************************************/\n";

	public static final String				FILE_FOOTER = "file_footer";
	public static final String				FILE_FOOTER_DFLT = "";
	
	public DefaultTemplateParameterProvider(ITemplateParameterProvider p) {
		super();

		set_defaults();
	
		if (p != null) {
			if (p.providesParameter(FILE_HEADER)) {
				setTag(FILE_HEADER, p.getParameterValue(FILE_HEADER, null));
			}
			if (p.providesParameter(FILE_FOOTER)) {
				setTag(FILE_HEADER, p.getParameterValue(FILE_FOOTER, null));
			}
		}
	}
	
	
	private void set_defaults() {
		setTag(FILE_HEADER, FILE_HEADER_DFLT);
		setTag(FILE_FOOTER, FILE_FOOTER_DFLT);
	}

}
