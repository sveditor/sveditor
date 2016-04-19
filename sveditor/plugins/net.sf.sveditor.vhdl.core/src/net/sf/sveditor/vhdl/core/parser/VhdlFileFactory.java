package net.sf.sveditor.vhdl.core.parser;

import java.io.InputStream;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import antlr.collections.AST;
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
				AST ast = p.getAST();
				System.out.println("ast=" + ast + " ast.child=" + ast.getNumberOfChildren());
				System.out.println("  sib=" + ast.getNextSibling());
				for (AST c = ast.getNextSibling(); c != null; c = c.getNextSibling()) {
					System.out.println("c=" + c);
				}

			} catch (TokenStreamException e) {
				e.printStackTrace();
			} catch (RecognitionException e) {
				e.printStackTrace();
			}
		}
	
		return ret;
	}

}
