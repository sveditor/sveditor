package net.sf.sveditor.ui.editor;

public interface SVDocumentPartitions {
	String SV_MULTILINE_COMMENT  = "__sv_multiline_comment";
	String SV_SINGLELINE_COMMENT = "__sv_multiline_comment";
	String SV_KEYWORD            = "__sv_keyword";
	String SV_STRING             = "__sv_string";
	
	
	String[] SV_PARTITION_TYPES = {
			SV_MULTILINE_COMMENT,
			SV_SINGLELINE_COMMENT
	};
	
	String SV_PARTITIONING = "__sv_partitioning";
}
