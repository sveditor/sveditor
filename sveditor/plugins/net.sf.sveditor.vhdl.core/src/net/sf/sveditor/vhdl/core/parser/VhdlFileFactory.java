package net.sf.sveditor.vhdl.core.parser;

import java.io.InputStream;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import net.sf.sveditor.core.db.SVDBFile;

public class VhdlFileFactory {
	
	public SVDBFile parse(InputStream in) {
		VhdlLexer lexer = new VhdlLexer(in);
		VhdlParser p = new VhdlParser(lexer);
		SVDBFile ret = null;
//		Tracker tracker = new Tracker();
	
		synchronized (VhdlParser.class) {

			try {
				p.design_file();
			} catch (TokenStreamException e) {
				e.printStackTrace();
			} catch (RecognitionException e) {
				e.printStackTrace();
			}
		}
	
		return ret;
	}

}
