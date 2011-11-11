package net.sf.sveditor.core.content_assist;

import java.util.ArrayList;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.SVDBModIfcDecl;

public class SVCompletionProposalUtils {
	// TODO: Need to have these parameters come from some sort of configuration file
	private int     				fTFMaxCharsPerLine      = 80;			// Number of characters before switching to multi-line mode
	private int     				fTFPortsPerLine 		= 0;			// Number of ports per line in multi-line mode
	private boolean 				fTFNamedPorts 			= true;			// When set, will have named ports, otherwise will just have names
	
	public SVCompletionProposalUtils() {
		
	}
	
	public void setMaxCharsPerLine(int max) {
		fTFMaxCharsPerLine = max;
	}
	
	public void setPortsPerLine(int max) {
		fTFPortsPerLine = max;
	}
	
	public void setNamedPorts(boolean named) {
		fTFNamedPorts = named;
	}
	
	private static String escapeId(String id) {
		StringBuilder sb = new StringBuilder(id);
		for (int i=0; i<sb.length(); i++) {
			if (sb.charAt(i) == '$') {
				sb.insert(i, '$');
				i++;
			}
		}
		return sb.toString();
	}
	
	public static String getLineIndent(
			String						doc,
			String						indent_incr) {
		StringBuilder doc_str = new StringBuilder(doc);
		
		// Trim any trailing content on the line. For example:
		//     if (<<EOL>>
		// becomes:
		//     <<EOL>>
		//
		int last_line_idx = doc_str.lastIndexOf("\n");
		String indent = "";
		if (last_line_idx != -1) {
			int end_line_idx = last_line_idx;
			// search forward to a non-whitespace char
			while (end_line_idx < doc_str.length() && 
					Character.isWhitespace(doc_str.charAt(end_line_idx))) {
				end_line_idx++;
			}
			indent = doc_str.substring(last_line_idx+1, end_line_idx);
		}
		
		return indent;
	}

	/**
	 * 
	 * @param tf
	 * @param subseq_line_indent -- Indent string for subsequent lines
	 * @param first_line_pos	 -- 
	 * @param subseq_line_pos
	 * @return
	 */
	public String createTFTemplate(
			SVDBTask 		tf,
			String			subseq_line_indent,
			int				first_line_pos,
			int				subseq_line_pos) {
		String newline = "\n" + subseq_line_indent;
		StringBuilder r = new StringBuilder();		// template text
		int curr_pos = first_line_pos;
		
		r.append(escapeId(SVDBItem.getName(tf)) + "(");
		
		int longest_string = 0;		// used to keep code nice and neat
//		int total_length   = 0;		// used to keep code nice and neat
		int param_count    = 0;		// used to keep code nice and neat
		
		ArrayList<String> all_ports = new ArrayList<String> ();
		ArrayList<String> all_types = new ArrayList<String> ();
		for (int i=0; i<tf.getParams().size(); i++) {
			SVDBParamPortDecl param = tf.getParams().get(i);
			for (ISVDBChildItem c : param.getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				all_ports.add(vi.getName());
				all_types.add(param.getTypeName());
				param_count ++;		// found another parameter
//				total_length += vi.getName().length();		// keep track of the length of the portlist
				if (vi.getName().length() > longest_string)  {
					longest_string = vi.getName().length();	// update the longest string
				}
			}
		}
		
		boolean multi_line_instantiation = false;
		if (
			(fTFMaxCharsPerLine != 0 && (first_line_pos + (longest_string * param_count)) > (fTFMaxCharsPerLine*7)/8) ||
			(fTFPortsPerLine != 0 && param_count > fTFPortsPerLine)
			) {
			multi_line_instantiation = true;
			r.append(newline);	// start ports on next line
			curr_pos = subseq_line_pos;
		}
		
		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<param_count; i++)  {
			StringBuilder padded_name = null;
			String name_str;
			// Padding is enabled if multi-line is triggered and
			// named ports are being used
			if (multi_line_instantiation && fTFNamedPorts)  {
				padded_name = new StringBuilder(all_ports.get(i));
				// TODO: is there a better way of adding padding?
				for (int cnt=padded_name.length(); cnt<longest_string+1; cnt++)  {
					padded_name.append(" ");
				}
				name_str = padded_name.toString();
			} else {
				name_str = all_ports.get(i);
			}

			// Only instantiate named ports if we need to
			if (fTFNamedPorts == true)  {
				// append .portname (
				r.append(".");
				r.append(name_str);
				r.append(" (");
				curr_pos += 3 + name_str.length(); 
			}
			// append ${porntmame} which will be replaced
//			r.append("${" + padded_name   + "}");
			r.append("${" + all_ports.get(i) + "}");
			curr_pos += 3 + all_ports.get(i).length();
			if (fTFNamedPorts == true)  {
				r.append(")");
				curr_pos++;
			}
	
			// Only add ", " on all but the last parameters
			if (i+1 < param_count)  {
				r.append(", ");
				curr_pos += 2;
				
				// Add \n if we have met the number of ports per line
				// or if we've exceeded the line max
				if ((fTFPortsPerLine != 0 && multi_line_instantiation && (((i+1) % fTFPortsPerLine) == 0)) ||
						(curr_pos > (7*fTFMaxCharsPerLine)/8)
						){ 
					// ML gets a CR after every port is instantiated
					r.append(newline);
					curr_pos = subseq_line_pos;
				}
			}
		}

		r.append(")");
		
		return r.toString();
	}

	
	/**
	 * 
	 * @param tf
	 * @param subseq_line_indent -- Indent string for subsequent lines
	 * @param first_line_pos	 -- 
	 * @param subseq_line_pos
	 * @return
	 */
	public String createModuleTemplate(
			SVDBModIfcDecl  tf,
			String			subseq_line_indent,
			int				first_line_pos,
			int				subseq_line_pos) {
		String newline = "\n" + subseq_line_indent;
		StringBuilder r = new StringBuilder();		// template text
		int curr_pos = first_line_pos;
		
		r.append(escapeId(SVDBItem.getName(tf)) + " ${" + escapeId(SVDBItem.getName(tf)) + "}" + " (");
		
		int longest_string = 0;		// used to keep code nice and neat
	//	int total_length   = 0;		// used to keep code nice and neat
		int param_count    = 0;		// used to keep code nice and neat
		
		ArrayList<String> all_ports = new ArrayList<String> ();
		ArrayList<String> all_types = new ArrayList<String> ();
		for (int i=0; i<tf.getPorts().size(); i++) {
			SVDBParamPortDecl param = tf.getPorts().get(i);
			for (ISVDBChildItem c : param.getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				all_ports.add(vi.getName());
				all_types.add(param.getTypeName());
				param_count ++;		// found another parameter
	//			total_length += vi.getName().length();		// keep track of the length of the portlist
				if (vi.getName().length() > longest_string)  {
					longest_string = vi.getName().length();	// update the longest string
				}
			}
		}
		
		boolean multi_line_instantiation = false;
		if (
			(fTFMaxCharsPerLine != 0 && (first_line_pos + (longest_string * param_count)) > (fTFMaxCharsPerLine*7)/8) ||
			(fTFPortsPerLine != 0 && param_count > fTFPortsPerLine)
			) {
			multi_line_instantiation = true;
			r.append(newline);	// start ports on next line
			curr_pos = subseq_line_pos;
		}
		
		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<param_count; i++)  {
			StringBuilder padded_name = null;
			String name_str;
			// Padding is enabled if multi-line is triggered and
			// named ports are being used
			if (multi_line_instantiation && fTFNamedPorts)  {
				padded_name = new StringBuilder(all_ports.get(i));
				// TODO: is there a better way of adding padding?
				for (int cnt=padded_name.length(); cnt<longest_string+1; cnt++)  {
					padded_name.append(" ");
				}
				name_str = padded_name.toString();
			} else {
				name_str = all_ports.get(i);
			}
	
			// Only instantiate named ports if we need to
			if (fTFNamedPorts == true)  {
				// append .portname (
				r.append(".");
				r.append(name_str);
				r.append(" (");
				curr_pos += 3 + name_str.length(); 
			}
			// append ${porntmame} which will be replaced
	//		r.append("${" + padded_name   + "}");
			r.append("${" + all_ports.get(i) + "}");
			curr_pos += 3 + all_ports.get(i).length();
			if (fTFNamedPorts == true)  {
				r.append(")");
				curr_pos++;
			}
	
			// Only add ", " on all but the last parameters
			if (i+1 < param_count)  {
				r.append(", ");
				curr_pos += 2;
				
				// Add \n if we have met the number of ports per line
				// or if we've exceeded the line max
				if ((fTFPortsPerLine != 0 && multi_line_instantiation && (((i+1) % fTFPortsPerLine) == 0)) ||
						(curr_pos > (7*fTFMaxCharsPerLine)/8)
						){ 
					// ML gets a CR after every port is instantiated
					r.append(newline);
					curr_pos = subseq_line_pos;
				}
			}
		}
	
		r.append(");");
		
		return r.toString();
	}

}
