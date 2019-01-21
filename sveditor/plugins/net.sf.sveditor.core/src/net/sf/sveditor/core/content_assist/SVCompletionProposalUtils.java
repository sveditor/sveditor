/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.content_assist;

import java.util.ArrayList;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMacroDefParam;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;

public class SVCompletionProposalUtils {
	// TODO: Need to have these parameters come from some sort of configuration file
	private int     				fTFMaxCharsPerLine      = 80;			// Number of characters before switching to multi-line mode
	private int     				fTFPortsPerLine 		= 0;			// Number of ports per line in multi-line mode
	private boolean 				fTFNamedPorts 			= true;			// When set, will have named ports, otherwise will just have names
	
	private int     				fModIfcInstMaxCharsPerLine	= 80;			// Number of characters before switching to multi-line mode
	private int     				fModIfcInstPortsPerLine 	= 1;			// Number of ports per line in multi-line mode
	private boolean					fModIfcInstNamedPorts		= true;
	
	public SVCompletionProposalUtils() {
		
	}
	
	public void setTFMaxCharsPerLine(int max) {
		fTFMaxCharsPerLine = max;
	}
	
	public void setTFPortsPerLine(int max) {
		fTFPortsPerLine = max;
	}
	
	public void setTFNamedPorts(boolean named) {
		fTFNamedPorts = named;
	}

	public void setModIfcInstMaxCharsPerLine(int max) {
		fModIfcInstMaxCharsPerLine = max;
	}
	
	public void setModIfcInstPortsPerLine(int max) {
		fModIfcInstPortsPerLine = max;
	}
	
	public void setModIfcInstNamedPorts(boolean named) {
		fModIfcInstNamedPorts = named;
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
		
		
		int longest_string = 0;		// used to keep code nice and neat
		int port_length   = 0;		// used to keep code nice and neat
		int port_count    = 0;		// used to keep code nice and neat
		
		ArrayList<String> all_ports = new ArrayList<String> ();
		ArrayList<String> all_types = new ArrayList<String> ();
		for (int i=0; i<tf.getParams().getParams().size(); i++) {
			SVDBParamPortDecl param = tf.getParams().getParams().get(i);
			for (ISVDBChildItem c : param.getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				all_ports.add(vi.getName());
				all_types.add(param.getTypeName());
				port_count ++;		// found another parameter
				port_length += vi.getName().length();		// keep track of the length of the portlist
				if (vi.getName().length() > longest_string)  {
					longest_string = vi.getName().length();	// update the longest string
				}
			}
		}
		
		boolean multi_line_instantiation = false;
		int multiplier = fTFNamedPorts ? 2 : 1;
		// Multi-line instantiation rules
		if	(((fTFMaxCharsPerLine != 0) && ((first_line_pos + (port_length*multiplier)+(2/*, */*multiplier)) > ((fTFMaxCharsPerLine*7)/8))) ||		// have a line length and we are probably longer than that line
			 ((fTFPortsPerLine != 0) && (port_count > fTFPortsPerLine))								// have a ports per line & param or port list > that that number
			) {
			multi_line_instantiation = true;
			curr_pos = subseq_line_pos;
		}
		else  {
			newline = "";
		}

		// Instantiate name
		r.append(escapeId(SVDBItem.getName(tf)) + "(" + newline);
		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<port_count; i++)  {
			StringBuilder padding = new StringBuilder("");
			String name_str = all_ports.get(i);
			// Padding is enabled if multi-line is triggered and
			// named ports are being used
			if (multi_line_instantiation)  {
				// TODO: is there a better way of adding padding?
				for (int cnt=name_str.length(); cnt<longest_string+1; cnt++)  {
					padding.append(" ");
				}
			}
	
			// Only instantiate named ports if we need to
			if (fTFNamedPorts == true)  {
				// append .portname (
				r.append(".");
				r.append(name_str + padding.toString());
				r.append(" (");
				curr_pos += 3 + name_str.length() + padding.toString().length(); 
			}
			// append ${porntmame} which will be replaced
			r.append("${" + all_ports.get(i) + "}" + padding.toString());
			curr_pos += 3 + all_ports.get(i).length() + padding.toString().length();
			if (fTFNamedPorts == true)  {
				r.append(")");
				curr_pos++;
			}
	
			// Only add ", " on all but the last parameters
			if (i+1 < port_count)  {
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
	 * @param md -- Macro/Define
	 * @param subseq_line_indent -- Indent string for subsequent lines
	 * @param first_line_pos	 -- 
	 * @param subseq_line_pos
	 * @return
	 */
	public String createMacroTemplate(
			SVDBMacroDef	md,
			String			subseq_line_indent,
			int				first_line_pos,
			int				subseq_line_pos) {
		String newline = "\n" + subseq_line_indent;
		StringBuilder r = new StringBuilder();		// template text
		int curr_pos = first_line_pos;
		
		
		int longest_string = 0;		// used to keep code nice and neat
		int port_length   = 0;		// used to keep code nice and neat
		int port_count    = 0;		// used to keep code nice and neat
		
		ArrayList<String> all_ports = new ArrayList<String> ();
		if (md.getParameters() != null)  {
			for (int i=0; i<md.getParameters().size(); i++) {
				SVDBMacroDefParam param = md.getParameters().get(i);
				all_ports.add(param.getName());
				port_count ++;		// found another parameter
				port_length += param.getName().length();		// keep track of the length of the portlist
				if (param.getName().length() > longest_string)  {
					longest_string = param.getName().length();	// update the longest string
				}
			}
		}
		
		boolean multi_line_instantiation = false;
		
		// Multi-line instantiation rules
		if	(((fTFMaxCharsPerLine != 0) && ((first_line_pos + (port_length)+(2/*, */)) > ((fTFMaxCharsPerLine*7)/8))) ||		// have a line length and we are probably longer than that line
				((fTFPortsPerLine != 0) && (port_count > fTFPortsPerLine))								// have a ports per line & param or port list > that that number
				) {
			multi_line_instantiation = true;
			curr_pos = subseq_line_pos;
		}
		else  {
			newline = "";
		}
		
		// Instantiate name
		if (port_count > 0)  {
			r.append(escapeId(SVDBItem.getName(md)) + "(" + newline);
		}
		else  {
			r.append(escapeId(SVDBItem.getName(md)) + newline);
		}
		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<port_count; i++)  {
			StringBuilder padding = new StringBuilder("");
			String name_str = all_ports.get(i);
			// Padding is enabled if multi-line is triggered and
			// named ports are being used
			if (multi_line_instantiation)  {
				// TODO: is there a better way of adding padding?
				for (int cnt=name_str.length(); cnt<longest_string+1; cnt++)  {
					padding.append(" ");
				}
			}
			
			// append ${porntmame} which will be replaced
			r.append("${" + all_ports.get(i) + "}" + padding.toString());
			curr_pos += 3 + all_ports.get(i).length() + padding.toString().length();
			
			// Only add ", " on all but the last parameters
			if (i+1 < port_count)  {
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
		
		if (port_count > 0)  {
			r.append(")");
		}
		
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
		
		
		int longest_string = 0;		// used to keep code nice and neat
		int port_len       = 0;		// used to keep code nice and neat
		int param_len      = 0;		// used to keep code nice and neat
		int port_count     = 0;		// used to keep code nice and neat
		int param_count    = 0;		// used to keep code nice and neat
		
		ArrayList<String> all_ports  = new ArrayList<String> ();
		ArrayList<String> all_types  = new ArrayList<String> ();
		ArrayList<String> all_params = new ArrayList<String> ();
		
		
		// Get a list of all parameters in the module
		for (int i=0; i<tf.getParameters().size(); i++) {
			String param_name = tf.getParameters().get(i).getName();
			all_params.add(param_name);
			param_count ++;		// found another parameter
			int len = param_name.length();
			param_len += len;		// keep track of length of parameter string
			if (len > longest_string)  {
				longest_string = len;	// update the longest string
			}
		}
		
		// Get a list of all ports in the module
		for (int i=0; i<tf.getPorts().size(); i++) {
			SVDBParamPortDecl param = tf.getPorts().get(i);
			for (ISVDBChildItem c : param.getChildren()) {
				SVDBVarDeclItem vi = (SVDBVarDeclItem)c;
				all_ports.add(vi.getName());
				all_types.add(param.getTypeName());
				port_count ++;		// found another parameter
				int len = vi.getName().length();
				port_len += len;			// keep track of total length of ports
				if (len > longest_string)  {
					longest_string = len;	// update the longest string
				}
			}
		}
		
		boolean multi_line_instantiation = false;
		int multiplier = fModIfcInstNamedPorts ? 2 : 1;
		// Multi-line instantiation rules
		if	(((fModIfcInstMaxCharsPerLine != 0) && ((first_line_pos + ((port_len + param_len)*multiplier)+(2/*, */*multiplier)) > ((fModIfcInstMaxCharsPerLine*7)/8))) ||		// have a line length and we are probably longer than that line
			 ((fModIfcInstPortsPerLine != 0) && ((port_count > fModIfcInstPortsPerLine) || (param_count > fModIfcInstPortsPerLine)))								// have a ports per line & param or port list > that that number
			) {
			multi_line_instantiation = true;
			curr_pos = subseq_line_pos;
		}
		else  {
			newline = "";
		}
		
		// Drop the module name
		r.append(escapeId(SVDBItem.getName(tf)));
		
		// Now add parameters
		if (param_count != 0)  {
			r.append(" #(" + newline);
			
			for (int i=0; i<param_count; i++)  {
				StringBuilder padding = new StringBuilder ("");
				String name_str = all_params.get(i);
				// Padding is enabled if multi-line is triggered and
				// named ports are being used
				if (multi_line_instantiation)  {
					// TODO: is there a better way of adding padding?
					for (int cnt=name_str.length(); cnt<longest_string+1; cnt++)  {
						padding.append(" ");
					}
				}
		
				// Only instantiate named ports if we need to
				if (fModIfcInstNamedPorts == true)  {
					r.append(".");
					r.append(name_str + padding.toString());
					r.append(" (");
					curr_pos += 3 + name_str.length() + padding.toString().length(); 
				}
				// append ${porntmame} which will be replaced
				r.append("${" + name_str + "}" + padding.toString());
				curr_pos += 3 + name_str.length() + padding.toString().length();
				if (fModIfcInstNamedPorts == true)  {
					r.append(")");
					curr_pos++;
				}
		
				// Only add ", " on all but the last parameters
				if (i+1 < param_count)  {
					r.append(", ");
					curr_pos += 2;
					
					// Add \n if we have met the number of ports per line
					// or if we've exceeded the line max
					if ((fModIfcInstPortsPerLine != 0 && multi_line_instantiation && (((i+1) % fModIfcInstPortsPerLine) == 0)) ||
							(curr_pos > (7*fModIfcInstMaxCharsPerLine)/8)
							){ 
						// ML gets a CR after every port is instantiated
						r.append(newline);
						curr_pos = subseq_line_pos;
					}
				}
			}
			// Close param list
			r.append(escapeId(newline + ")"));
		}

		// Add the instance name
		r.append(" ${" + escapeId(SVDBItem.getName(tf)) + "}" + " (" + newline);
		// if we have a newline, reset the current position
		if (!newline.isEmpty())
			curr_pos = subseq_line_pos;

		// Now create the string & port list - note that we are padding to the longest string with spaces
		for (int i=0; i<port_count; i++)  {
			StringBuilder padding = new StringBuilder("");
			String name_str = all_ports.get(i);
			// Padding is enabled if multi-line is triggered and
			// named ports are being used
			if (multi_line_instantiation)  {
				// TODO: is there a better way of adding padding?
				for (int cnt=name_str.length(); cnt<longest_string+1; cnt++)  {
					padding.append(" ");
				}
			}
	
			// Only instantiate named ports if we need to
			if (fModIfcInstNamedPorts == true)  {
				// append .portname (
				r.append(".");
				r.append(name_str + padding.toString());
				r.append(" (");
				curr_pos += 3 + name_str.length() + padding.toString().length(); 
			}
			// append ${porntmame} which will be replaced
			r.append("${" + all_ports.get(i) + "}" + padding.toString());
			curr_pos += 3 + all_ports.get(i).length() + padding.toString().length();
			if (fModIfcInstNamedPorts == true)  {
				r.append(")");
				curr_pos++;
			}
	
			// Only add ", " on all but the last parameters
			if (i+1 < port_count)  {
				r.append(", ");
				curr_pos += 2;
				
				// Add \n if we have met the number of ports per line
				// or if we've exceeded the line max
				if ((fModIfcInstPortsPerLine != 0 && multi_line_instantiation && (((i+1) % fModIfcInstPortsPerLine) == 0)) ||
						(curr_pos > (7*fModIfcInstMaxCharsPerLine)/8)
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
