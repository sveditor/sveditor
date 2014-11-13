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


package net.sf.sveditor.core.parser;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.stmt.SVDBVarDimItem;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVGateInstantiationParser extends SVParserBase {
	
	public SVGateInstantiationParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		SVDBModIfcInst item = null;
		int max_ports = 0;
		int min_ports = 0;
		int max_strengths = 0;      // max number of strengths
		int max_delays    = 0;      // max number of delays

		// Gates                   - Allows strengths            - and, nand, or, nor,xor, xnor, buf, not
		// Three State Drivers     - Allows strengths            - bufif0 ,bufif1, notif0,notif1
		// MOS Switches            - No strengths                - nmos,pmos,cmos, rnmos,rpmos,rcmos
		// Bi-directional switches - No strengths, non resistive - tran, tranif0, tranif1
		// Bi-directional switches - No strengths, resistive     - rtran,rtranif0, rtranif1
		// Bi-directional switches - Allows strengths            - pullup pulldown

		// <gate-declaration> ::= <component> <drive_strength>? <delay>? <gate_instance> <,?<gate_instance..>> ;
		// Examples:
		// Gate level instantiations
		// nor (highz1, strong0) #(2:3:5) InstanceName (out, in1, in2);
		// instantiates a nor gate with out
		// strength of highz1 (for 1) and
		// strong0 for 0 #(2:3:5) is the
		// min:typ:max delay
		// pullup1 (strong1) net1;
		// instantiates a logic high pullup
		// cmos (out, data, ncontrol, pcontrol);
		// MOS devices
		
		// cmos gates have 4 terminals
		SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
		String primitive_name = type.getName();
		SVDBLocation start = fLexer.getStartLocation();

		// These primitives have the following port order
		// cmos (out, data_in, ncontrol, pcontrol)
		if ((primitive_name.equals("cmos")) || 
		   (primitive_name.equals("rcmos")))  { 
			min_ports = 4;
			max_ports = 4;
			max_delays= 3;
		}
		// These primitives have the following port order
		// pmos (out, data_in, control)
		else if ((primitive_name.equals("nmos")) || 
			(primitive_name.equals("pmos")) || 
			(primitive_name.equals("rnmos")) || 
			(primitive_name.equals("rpmos")))  {
			min_ports = 3;
			max_ports = 3;
			max_delays = 3;
		}
		// These primitives are:
	    // and (out, in1, in2, in3, ...)
		else if ((primitive_name.equals("and" )) ||
		         (primitive_name.equals("nand")) ||
		         (primitive_name.equals("or"  )) ||
		         (primitive_name.equals("nor" )) ||
		         (primitive_name.equals("xor" )) ||
		         (primitive_name.equals("xnor")))  {
			min_ports = 3;
			max_ports = -1;
			max_strengths = 2;      // max number of strengths
			max_delays    = 2;      // max number of delays
		}
		// These primitives have format
		// buf (out1, out2,..., in);
		else if ((primitive_name.equals("buf")) ||
		         (primitive_name.equals("not")))  {
			min_ports = 2;
			max_ports = -1;
			max_strengths = 2;      // max number of strengths
			max_delays    = 2;      // max number of delays
		}
		// These primitive have the following format
		// bufif0 (out, in, control)
		else if ((primitive_name.equals("bufif0")) ||
                 (primitive_name.equals("bufif1")) ||
                 (primitive_name.equals("notif0")) ||
                 (primitive_name.equals("notif1")))  {
			min_ports = 3;
			max_ports = 3;
			max_strengths = 2;      // max number of strengths
			max_delays    = 3;      // max number of delays
		}
		// These primitive have the following format
		// tranif (inout, inout, control)
		else if ((primitive_name.equals("tranif0" )) ||
	             (primitive_name.equals("tranif1" )) ||
		         (primitive_name.equals("rtranif0")) ||
		         (primitive_name.equals("rtranif1")))  {
			min_ports = 3;
			max_ports = 3;
			max_delays    = 3;      // max number of delays
		}
		// These primitive have the following format
		// tran (inout, inout, control)
		else if ((primitive_name.equals("tran"    )) ||
				(primitive_name.equals("rtran"   )))  {
			min_ports = 2;
			max_ports = 2;
			max_delays    = 3;      // max number of delays
		}
		// These primitive have the following format
		// pullup (out)
		else if ((primitive_name.equals("pullup"  )) ||
		         (primitive_name.equals("pulldown")))  {
			min_ports = 1;
			max_ports = 1;
			max_strengths = 2;      // max number of strengths
			max_delays    = 3;      // max number of delays
		}
		// name that we don't have 
		else  {
			error("[Internal Error] gate-type " + primitive_name + " not recognized");
		}

		// Check if we have strengths ...
		if ((max_strengths != 0) && (fLexer.peekOperator("(")))  {
			SVToken tok = fLexer.consumeToken();
			if (fLexer.peekKeyword(SVKeywords.fStrength))  {
				// TODO: handle / store strengths somewhere
				String strengths = parsers().SVParser().strengths(max_strengths);
			}
			else  {
				// TODO: Put "(" back
				fLexer.ungetToken(tok);
			}
		}
		
		// Get Delay block if any
		if (fLexer.peekOperator("#")) {
			// TODO: handle/store delay somewhere
			parsers().SVParser().delay_n(max_delays);
		}

		item = new SVDBModIfcInst(type);
		item.setLocation(start);
		
		// Now, a series of switch instances
		while (fLexer.peek() != null) {
			String name = ""; 
			start = fLexer.getStartLocation();
			if (fLexer.peekId()) {
				name = fLexer.eatToken();
			}
			SVDBModIfcInstItem inst = new SVDBModIfcInstItem(name);
			inst.setLocation(start);
			List<SVDBVarDimItem> arraydims = null;
			if (fLexer.peekOperator("["))  {
				// Array type
				// TODO: What should we do with the array dimensions?
				arraydims = parsers().dataTypeParser().var_dim();
			}
			item.addInst(inst);
			
			fLexer.readOperator("(");
			
			boolean terminals_read = false;
			int num_ports = 0;
			while (terminals_read == false)  {
				// TODO: output_terminal
				parsers().exprParser().expression();
				num_ports ++;
				if (fLexer.peekOperator(","))  {
					fLexer.readOperator(",");
				}
				else  {
					terminals_read = true;
				}
			}

			// Check if there is no maximum number of ports
			if (max_ports == -1)  {
				max_ports = num_ports;
			}
			
			// check if the ports are what we expect
			if ((num_ports > max_ports) || (num_ports < min_ports))  {
				error("[Internal Error] Primitive port list error: gate-type " + primitive_name + " has '" + num_ports + "' port instead of between '" + min_ports + "' and '" + max_ports + "' ports" );
			}
			fLexer.readOperator(")");
			
			if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
			} else {
				break;
			}
		} 
//		else {
//			error("[Internal Error] gate-type " + fLexer.peek() + " not recognized");
//		}

		fLexer.readOperator(";");

		parent.addChildItem(item);
	}

}
