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
package org.sveditor.core.tagproc;

import java.text.SimpleDateFormat;
import java.util.Date;

public class DynamicTemplateParameterProvider implements
		ITemplateParameterProvider {

	public boolean providesParameter(String id) {
		return (id.equals("date") || id.equals("user"));
	}

	public String getParameterValue(String id, String arg) {
		if (id.equals("user")) {
			return System.getProperty("user.name");
		} else if (id.equals("date")) {
			SimpleDateFormat format;
			if (arg != null) {
				format = new SimpleDateFormat(arg);
			} else {
				format = new SimpleDateFormat("MM/dd/YYYY");
			}
			return format.format(new Date());
		} else {
			return null;
		}
	}

}
