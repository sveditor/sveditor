package net.sf.sveditor.core.content_assist;

import java.util.ArrayList;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.indent.ISVIndenter;

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

	public String createTFTemplate(
			SVDBTask 		tf,
			String			next_line_indent) {
		String newline = "\n" + next_line_indent;
		StringBuilder r = new StringBuilder();		// template text
		
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
		if ((longest_string * param_count)> fTFMaxCharsPerLine/2)  {
			multi_line_instantiation = true;
			r.append(newline);	// start ports on next line
		}
		
		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<param_count; i++)  {
			StringBuilder padded_name = new StringBuilder(all_ports.get(i));
			if (multi_line_instantiation)  {
				// TODO: is there a better way of adding padding?
				for (int cnt=padded_name.length(); cnt<longest_string+1; cnt++)  {
					padded_name.append(" ");
				}
			}

			// Only instantiate named ports if we need to
			if (fTFNamedPorts == true)  {
				// append .portname (
				r.append("." + padded_name   + " (");
			}
			// append ${porntmame} which will be replaced
			r.append("${" + padded_name   + "}");
			if (fTFNamedPorts == true)  {
				r.append(")");
			}
	
			// Only add ", " on all but the last parameters
			if (i < (param_count -1))  {
				r.append(", ");
				// Add \n if we have met the number of ports per line
				if (fTFPortsPerLine > 0 && multi_line_instantiation && (((i+1) % fTFPortsPerLine) == 0))  { 
					// ML gets a CR after every port is instantiated
					r.append(newline);
				}
			}
		}

		r.append(")");
		
		return r.toString();
	}

}
