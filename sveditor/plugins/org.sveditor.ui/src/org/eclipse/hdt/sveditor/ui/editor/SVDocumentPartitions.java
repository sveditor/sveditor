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


package org.sveditor.ui.editor;


public interface SVDocumentPartitions {
	String SV_MULTILINE_COMMENT  = "__sv_multiline_comment";
	String SV_SINGLELINE_COMMENT = "__sv_singleline_comment";
	String SV_KEYWORD            = "__sv_keyword";
	String SV_STRING             = "__sv_string";
	String SV_CODE				 = "__sv_code";
	
	
	String[] SV_PARTITION_TYPES = {
			SV_MULTILINE_COMMENT,
			SV_SINGLELINE_COMMENT,
			SV_CODE
	};
	
	String SV_PARTITIONING = "__sv_partitioning";
}
