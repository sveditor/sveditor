package net.sf.sveditor.core.vhdl.parser;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Architecture_bodyContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Configuration_declarationContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Design_fileContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Design_unitContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Entity_declarationContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Library_clauseContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Package_bodyContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Package_declarationContext;
import net.sf.sveditor.core.vhdl.parser.vhdlParser.Use_clauseContext;

public class VHDLFileFactory extends vhdlBaseVisitor<ISVDBChildItem> {
	VHFactories				fFactories;
	
	public VHDLFileFactory() {
		fFactories = new VHFactories();
	}
	

	public SVDBFile parse(
			InputStream			in,
			String				filename,
			List<SVDBMarker>	markers) {
		SVDBFile ret = new SVDBFile();

		try {
			vhdlLexer l = new vhdlLexer(new ANTLRInputStream(in));
			vhdlParser p = new vhdlParser(new CommonTokenStream(l));
			
			Design_fileContext root = p.design_file();
			
			for (Design_unitContext ctx : root.design_unit()) {
				ISVDBChildItem item = ctx.accept(this);
				
				if (item != null) {
					ret.addChildItem(item);
				}
			}
			
			System.out.println("Design_fileContext: " + root);
			root.accept(this);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return ret;
	}
	
	
	@Override
	public ISVDBChildItem visitLibrary_clause(Library_clauseContext ctx) {
		// TODO Auto-generated method stub
		return super.visitLibrary_clause(ctx);
	}

	@Override
	public ISVDBChildItem visitUse_clause(Use_clauseContext ctx) {
		// TODO Auto-generated method stub
		return super.visitUse_clause(ctx);
	}

	@Override
	public ISVDBChildItem visitEntity_declaration(Entity_declarationContext ctx) {
		return fFactories.entity().visit(ctx);
	}

	@Override
	public ISVDBChildItem visitConfiguration_declaration(Configuration_declarationContext ctx) {
		// TODO Auto-generated method stub
		return super.visitConfiguration_declaration(ctx);
	}

	@Override
	public ISVDBChildItem visitPackage_declaration(Package_declarationContext ctx) {
		// TODO Auto-generated method stub
		return super.visitPackage_declaration(ctx);
	}

	@Override
	public ISVDBChildItem visitArchitecture_body(Architecture_bodyContext ctx) {
		// TODO Auto-generated method stub
		return super.visitArchitecture_body(ctx);
	}

	@Override
	public ISVDBChildItem visitPackage_body(Package_bodyContext ctx) {
		// TODO Auto-generated method stub
		return super.visitPackage_body(ctx);
	}
	

}
