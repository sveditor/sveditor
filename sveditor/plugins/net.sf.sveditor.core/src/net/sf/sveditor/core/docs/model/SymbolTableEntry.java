package net.sf.sveditor.core.docs.model;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

enum SymbolType { 
	CLASS, 
	PKG, 
	CLASS_MEMBER,
	MOD_PROG,
	MOD_PROG_MEMBER} ;

public class SymbolTableEntry {
	
	private String symbol ;
	private String pkgName ;
	private String className ;  // fixme: this is actually the class/mod/prog name. rename to... er, "typeName" 
	private String memberName ;
	private String topicType ;
	private String file ;
	
	private SymbolType symbolType ;
	private boolean isDocumented ;
	
	private ISVDBIndex svdbIndex ; // FIXME: is it necessary to carry this around?
	private SVDBDeclCacheItem declCacheItem ; // FIXME: is it necessary to carry this around?
	private DocFile docFile;
	
	public static SymbolTableEntry createPkgEntry(String pkgName, ISVDBIndex svdbIndex, String file, SVDBDeclCacheItem declCacheItem) {
		String symbolName = pkgName ;
		SymbolTableEntry result = new SymbolTableEntry(symbolName, SymbolType.PKG) ;
		result.setPkgName(pkgName) ;
		result.setSvdbIndex(svdbIndex) ;
		result.setFile(file) ;
		result.setDeclCacheItem(declCacheItem) ;
		return result ;
	}

	public static SymbolTableEntry createModProgEntry(String pkgName, String file, SVDBDeclCacheItem declCacheItem) {
		String symbolName = pkgName ;
		SymbolTableEntry result = new SymbolTableEntry(symbolName, SymbolType.PKG) ;
		result.setPkgName(pkgName) ;
		result.setFile(file) ;
		result.setDeclCacheItem(declCacheItem) ;
		return result ;
	}
	
	public static SymbolTableEntry createClassEntry(String pkgName, String className, ISVDBIndex svdbIndex, String file, SVDBDeclCacheItem declCacheItem) {
		String symbolName = String.format("%s::%s", pkgName, className) ;
		SymbolTableEntry result = new SymbolTableEntry(symbolName, SymbolType.CLASS) ;
		result.setPkgName(pkgName) ;
		result.setClassName(className) ;
		result.setSvdbIndex(svdbIndex) ;
		result.setFile(file) ;
		result.setDeclCacheItem(declCacheItem) ;
		return result ;
	}
	
	public static SymbolTableEntry createClassMemberEntry(String pkgName, String className, String memberName, ISVDBIndex svdbIndex, String file) {
		String symbolName = String.format("%s::%s::%s", pkgName, className, memberName) ;
		SymbolTableEntry result = new SymbolTableEntry(symbolName, SymbolType.CLASS_MEMBER) ;
		result.setPkgName(pkgName) ;
		result.setClassName(className) ;
		result.setMemberName(memberName) ;
		result.setSvdbIndex(svdbIndex) ;
		result.setFile(file) ;
		return result ;
	}
	
	public static SymbolTableEntry createModProgMemberEntry(String modProgName, String memberName, ISVDBIndex svdbIndex, String file) {
		String symbolName = String.format("%s::%s", modProgName, memberName) ;
		SymbolTableEntry result = new SymbolTableEntry(symbolName, SymbolType.MOD_PROG_MEMBER) ;
		result.setClassName(modProgName) ;
		result.setMemberName(memberName) ;
		result.setSvdbIndex(svdbIndex) ;
		result.setFile(file) ;
		return result ;
	}
	
	public SymbolTableEntry(String symbol, SymbolType symbolType) {
		this.symbol = symbol ;
		this.symbolType = symbolType ;
		this.pkgName = null ;
		this.memberName = null ;
		this.svdbIndex = null ;
		this.topicType = "unknown" ;
		this.declCacheItem = null ;
		this.isDocumented = false ;
	}
	
	public String getMemberName() {
		return memberName;
	}

	public void setMemberName(String memberName) {
		this.memberName = memberName;
	}

	
	public String getSymbol() {
		return symbol;
	}

	public void setSymbol(String symbol) {
		this.symbol = symbol;
	}

	public String getPkgName() {
		return pkgName;
	}

	public void setPkgName(String pkgName) {
		this.pkgName = pkgName;
	}

	public String getClassName() {
		return className;
	}

	public void setClassName(String className) {
		this.className = className;
	}

	public SymbolType getSymbolType() {
		return symbolType;
	}

	public void setSymbolType(SymbolType symbolType) {
		this.symbolType = symbolType;
	}

	public ISVDBIndex getSvdbIndex() {
		return svdbIndex;
	}

	public void setSvdbIndex(ISVDBIndex svdbIndex) {
		this.svdbIndex = svdbIndex;
	}

	public SVDBDeclCacheItem getDeclCacheItem() {
		return declCacheItem;
	}

	public void setDeclCacheItem(SVDBDeclCacheItem declCacheItem) {
		this.declCacheItem = declCacheItem;
	}
	
	public boolean isDocumented() {
		return isDocumented;
	}

	public void setDocumented(boolean isDocumented) {
		this.isDocumented = isDocumented;
	}

	public String getDocPath() {
		if(this.docFile != null) {
			return docFile.getDocPath() ;
		} else {
			return "UNKNOWN-DOC-PATH-FOR-SYMBOL-" + getSymbol() ;
		}
	}

	public void setDocFile(DocFile docFile) {
	  this.docFile = docFile ;	
	}
	
	public DocFile getDocFile() {
		return this.docFile ;
	}
	
	public String getTopicType() {
		return topicType;
	}

	public void setTopicType(String topicType) {
		this.topicType = topicType;
	}

	public static String cleanSymbol(String symbol) {
		String result = symbol ;
		result = result.replaceAll("\\(.*\\)", "") ; // Remove parens on tasks/functions
		result = result.replaceAll("\\.","::") ; // Replace . with ::
		result = result.replaceAll("\\s*#\\s*", "") ; // Remove parameter stuff
		return result ;
		
	}
	
	public String getFile() {
		return file;
	}

	public void setFile(String file) {
		this.file = file;
	}


}
