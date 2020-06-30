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


package org.eclipse.hdt.sveditor.ui.argfile.editor;


public interface SVArgFileDocumentPartitions {
	String SV_ARGFILE_MULTILINE_COMMENT  = "__sv_argfile_multiline_comment";
	String SV_ARGFILE_SINGLELINE_COMMENT = "__sv_argfile_singleline_comment";
	String SV_ARGFILE_KEYWORD            = "__sv_argfile_keyword";
	
	String[] SV_ARGFILE_PARTITION_TYPES = {
			SV_ARGFILE_MULTILINE_COMMENT,
			SV_ARGFILE_SINGLELINE_COMMENT,
			SV_ARGFILE_KEYWORD
	};
	
	String SV_ARGFILE_PARTITIONING = "__sv_argfile_partitioning";
}
