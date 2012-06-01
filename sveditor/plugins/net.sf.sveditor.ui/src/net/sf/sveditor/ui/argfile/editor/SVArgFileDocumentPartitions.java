/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.argfile.editor;


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
