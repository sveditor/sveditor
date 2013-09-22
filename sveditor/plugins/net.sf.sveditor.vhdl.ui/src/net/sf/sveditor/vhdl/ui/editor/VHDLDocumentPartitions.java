package net.sf.sveditor.vhdl.ui.editor;


public interface VHDLDocumentPartitions {

	String VHD_COMMENT = "__vhd_comment";
	String VHD_KEYWORD = "__vhd_keyword";
	String VHD_STRING  = "__vhd_string";
	String VHD_CODE    = "__vhd_code";
	
	String [] VHD_PARTITION_TYPES = {
			VHD_COMMENT,
			VHD_STRING
	};
	
	String VHD_PARTITIONING = "__vhd_partitioning";
}
