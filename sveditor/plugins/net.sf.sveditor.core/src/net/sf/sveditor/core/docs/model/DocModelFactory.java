/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.docs.model;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBDocComment;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;


public class DocModelFactory {
	
	private LogHandle fLog ;
	private SymbolTable fSymbolTable ;
	
	private class DocModelFactoryException extends Exception {
		private static final long serialVersionUID = -6656720421849741060L;
		public DocModelFactoryException(String msg) {
			super(msg) ;
		}
	}
	
	public DocModelFactory() {
		fLog = LogFactory.getLogHandle("DocModelFactory") ;
		fSymbolTable = new SymbolTable() ;
	}

	public DocModel build(DocGenConfig cfg) {
		DocModel model = new DocModel() ;
		IDocCommentParser docCommentParser = new DocCommentParser(model.getDocTopics()) ;
		try {
			buildInitialSymbolTableFromSVDB(cfg, model) ;
			spinThroughComments(cfg, model, docCommentParser) ;
			gatherPackages(cfg, model) ;
		} catch (Exception e) {
			fLog.error("Document model build failed: " + e.toString()) ;
		}
		return model ;
	}

	private void spinThroughComments(DocGenConfig cfg, DocModel model, IDocCommentParser docCommentParser) {
		HashSet<ISVDBIndex> visitedIndex = new HashSet<ISVDBIndex>() ;
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> pkgTuple: cfg.getSelectedPackages()) {
			ISVDBIndex index = pkgTuple.second() ;
			if(!visitedIndex.contains(index)) {
				visitedIndex.add(index) ;
				for(String file: index.getFileList(new NullProgressMonitor())) {
					DocItem parent = null ;
					SVDBFile ppFile = index.getCache().getPreProcFile(new NullProgressMonitor(), file) ;
					if(ppFile == null) {
						fLog.error("Failed to find pre proc file for: " + file) ;
					} else {
						fLog.debug(ILogLevel.LEVEL_MID,"Search for doc comments in: " + file) ;
						String path = file ;
						if (path.startsWith("${workspace_loc}")) {
							path = path.substring("${workspace_loc}".length()) ;
						}
						DocFile docFile = new DocFile(file) ;
						parent = docFile ;
						docFile.setDocPath(path) ;
						boolean fileHasDocs = false ;
						for(ISVDBChildItem child: ppFile.getChildren()) {
							if(child instanceof SVDBDocComment) {
								Set<DocItem> docTopics = new HashSet<DocItem>() ; // FIXME: this needs to be ordered
								SVDBDocComment docCom = (SVDBDocComment)child ;
								fLog.debug(ILogLevel.LEVEL_MID,"Found comment: " + docCom.getName()) ;
								docCommentParser.parse(docCom.getRawComment(),docTopics) ;
								for(DocItem topic: docTopics) {
									fLog.debug(ILogLevel.LEVEL_MID,"Found topic: " + topic.getName()) ;
									switch(topic.getType()) {
										case CLASS:
										case PACKAGE:
											parent = docFile ;
											break ;
										default:
											break ;
									}
									parent.addChild(topic) ;
									fileHasDocs = true ;
									switch(topic.getType()) {
										case TASK:
										case FUNC:
										case VARDECL:
											break ;
										case CLASS:
										case PACKAGE:	
										default:
											parent = topic ;
											fLog.debug(ILogLevel.LEVEL_MID,"Parent changed to ("+ topic.getName() + ")") ;
											break ;
									}
								}
							}
						}						
						if(fileHasDocs) {
							model.getDocFiles().put(file, docFile) ;
						}
					}
				}
			}
		}
	}

	private void buildInitialSymbolTableFromSVDB(DocGenConfig cfg, DocModel model) {
		
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> pkgTuple: cfg.getSelectedPackages()) {
			SVDBDeclCacheItem pkgDeclCacheItem = pkgTuple.first() ;
			ISVDBIndex pkgSvdbIndex = pkgTuple.second() ;
			SymbolTableEntry pkgSTE = 
					SymbolTableEntry.createPkgEntry(pkgDeclCacheItem.getName(), pkgSvdbIndex, pkgDeclCacheItem) ;
			fSymbolTable.addSymbol(pkgSTE) ;
			gatherPackageSymbols(cfg, model, pkgDeclCacheItem, pkgSvdbIndex) ;
		}
		fSymbolTable.dumpSymbols() ;
			
	}

	private void gatherPackageSymbols(DocGenConfig cfg, 
										DocModel model, 
										SVDBDeclCacheItem pkgDeclCacheItem, 
										ISVDBIndex pkgSvdbIndex) {
		
		List<SVDBDeclCacheItem> pkgDecls = pkgDeclCacheItem.getParent().findPackageDecl(new NullProgressMonitor(), pkgDeclCacheItem) ; 
		if(pkgDecls != null) {
			for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
				if(pkgDecl.getType() == SVDBItemType.ClassDecl) {
					SymbolTableEntry classSTE = 
							SymbolTableEntry.createClassEntry(pkgDeclCacheItem.getName(), pkgDecl.getName(), pkgSvdbIndex, pkgDecl) ;
					fSymbolTable.addSymbol(classSTE) ;
					gatherClassSymbols(cfg,model,pkgSvdbIndex,pkgDeclCacheItem,pkgDecl) ;
				}
			}
		} else {
			fLog.debug(ILogLevel.LEVEL_MID,"No decls found for pkg(" + pkgDeclCacheItem.getName() + ")") ;
		}
	}

	private void gatherClassSymbols(DocGenConfig cfg, DocModel model,
			ISVDBIndex pkgSvdbIndex, SVDBDeclCacheItem pkgDeclCacheItem,
			SVDBDeclCacheItem classDeclCacheItem) {
		
		SVDBClassDecl svdbClassDecl = (SVDBClassDecl)classDeclCacheItem.getSVDBItem() ;
		for(ISVDBChildItem ci: svdbClassDecl.getChildren()) {
			if(ci.getType() == SVDBItemType.Task) {
				SVDBTask svdbTask = (SVDBTask)ci ;
				SymbolTableEntry taskSTE =
						SymbolTableEntry.createClassMemberEntry(pkgDeclCacheItem.getName(), 
								classDeclCacheItem.getName(), 
								svdbTask.getName(), 
								pkgSvdbIndex) ;
				fSymbolTable.addSymbol(taskSTE) ;
			} else if(ci.getType() == SVDBItemType.Function) {
				SVDBFunction svdbFunction = (SVDBFunction)ci ;
				SymbolTableEntry funcSTE =
						SymbolTableEntry.createClassMemberEntry(pkgDeclCacheItem.getName(), 
								classDeclCacheItem.getName(), 
								svdbFunction.getName(), 
								pkgSvdbIndex) ;
				fSymbolTable.addSymbol(funcSTE) ;
			} else if(ci.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt varDecl = (SVDBVarDeclStmt)ci ;
				for(ISVDBChildItem varItem: varDecl.getChildren()) {
					if(varItem instanceof SVDBVarDeclItem) {
						SVDBVarDeclItem varDeclItem = (SVDBVarDeclItem)varItem ;
						SymbolTableEntry varSTE =
								SymbolTableEntry.createClassMemberEntry(pkgDeclCacheItem.getName(), 
										classDeclCacheItem.getName(), 
										varDeclItem.getName(), 
										pkgSvdbIndex) ;
						fSymbolTable.addSymbol(varSTE) ;
					}
				}
			}
		}		
		
	}

	private void gatherPackages(DocGenConfig cfg, DocModel model) throws DocModelFactoryException {
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> pkgTuple: cfg.getSelectedPackages()) {
			SVDBDeclCacheItem pkg = pkgTuple.first() ;
			Map<String, Map<String, DocClassItem>> classMapByPkg = model.getClassMapByPkg() ;
			classMapByPkg.put(pkg.getName(), new HashMap<String, DocClassItem>()) ;
			if(pkg.getParent() == null) {
				throw new DocModelFactoryException("Package had no parent index: " + pkg.getName()) ;
			}
			gatherPackageClasses(model, pkg, classMapByPkg, pkgTuple.second());			
		}
	}

	private void gatherPackageClasses(DocModel model, 
									  SVDBDeclCacheItem pkg,
									  Map<String, Map<String, DocClassItem>> classMapByPkg, ISVDBIndex isvdbIndex)
			throws DocModelFactoryException {
		List<SVDBDeclCacheItem> pkgDecls = pkg.getParent().findPackageDecl(new NullProgressMonitor(), pkg) ; 
		Map<String, DocFile> docFiles = model.getDocFiles() ;
		if(pkgDecls != null) {
			for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
				SVDBFile ppFile = isvdbIndex.getCache().getPreProcFile(new NullProgressMonitor(), pkgDecl.getFile().getFilePath()) ;
				if(ppFile != null) {
					String symbol = String.format("%s::%s", pkg.getName(), pkgDecl.getName()) ;
					if(docFiles.containsKey(pkgDecl.getFile().getFilePath())) {
						DocFile docFile = docFiles.get(pkgDecl.getFile().getFilePath()) ;
						for(DocItem docItem: docFile.getChildren()) {
							if(docItem.getName().equals(pkgDecl.getName())) {
								fLog.debug(ILogLevel.LEVEL_MID, String.format("Found doc item for %s",symbol)) ;
								SymbolTableEntry symbolEntry = fSymbolTable.getSymbol(symbol) ;
								if(symbolEntry == null) {
									fLog.error("Couldn't find symbol entry for symbol(" + symbol + ")") ;
								} else {
									symbolEntry.setDocPath(docFile.getDocPath()) ;
									symbolEntry.setDocumented(true) ;
									//								docFiles.get(pkgDecl.getFile().getFilePath()).setEnclosingPkg(pkg.getName()) ;
									docItem.setEnclosingPkg(pkg.getName()) ;
									if(pkgDecl.getType() == SVDBItemType.ClassDecl && docItem instanceof DocClassItem) {
										indexClass((DocClassItem)docItem,model) ;  
										gatherClassMembers((DocClassItem)docItem, pkg, pkgDecl, model, isvdbIndex, docFile, ppFile) ;
									}
								}
								break ;
							}
						}
					} else {
						// TODO: provide user option to include undocumented package members
						//   which would require creating the DocItems here and inserting
						//   them into the DocFile accordingly 
					}
				}
			}
		} else {
			fLog.debug("Package declarations for \"" + pkg.getName() + "\" not found");
		}
	}
	
	private void gatherClassMembers(DocClassItem classDocItem, 
									SVDBDeclCacheItem pkgDeclCacheItem, 
									SVDBDeclCacheItem classDeclCacheItem, 
									DocModel model, 
									ISVDBIndex isvdbIndex,
									DocFile docFile,
									SVDBFile ppFile ) {
		SVDBClassDecl svdbClassDecl = (SVDBClassDecl)classDeclCacheItem.getSVDBItem() ;
		for(ISVDBChildItem ci: svdbClassDecl.getChildren()) {
			if(ci.getType() == SVDBItemType.Task) {
				SVDBTask svdbTask = (SVDBTask)ci ;
				for(DocItem docItem: classDocItem.getChildren()) {
					if(docItem.getName().equals(svdbTask.getName())) {
						docItem.setEnclosingClass(classDeclCacheItem.getName()) ;
						docItem.setEnclosingPkg(pkgDeclCacheItem.getName()) ;
						String symbol = docItem.getQualifiedName() ;
						SymbolTableEntry symbolEntry = fSymbolTable.getSymbol(symbol) ;
						if(symbolEntry == null) {
							fLog.error("Couldn't find symbol entry for symbol(" + symbol + ")") ;
						} else {
							fLog.debug(ILogLevel.LEVEL_MID, String.format("Found doc item for class member %s",symbol)) ;
							symbolEntry.setDocPath(docFile.getDocPath()) ;
							symbolEntry.setDocumented(true) ;
						}
						break ;
					}
				}
			}
			if(ci.getType() == SVDBItemType.Function) {
				SVDBFunction svdbFunc = (SVDBFunction)ci ;
				for(DocItem docItem: classDocItem.getChildren()) {
					if(docItem.getName().equals(svdbFunc.getName())) {
						docItem.setEnclosingClass(classDeclCacheItem.getName()) ;
						docItem.setEnclosingPkg(pkgDeclCacheItem.getName()) ;
						String symbol = docItem.getQualifiedName() ;
						SymbolTableEntry symbolEntry = fSymbolTable.getSymbol(symbol) ;
						if(symbolEntry == null) {
							fLog.error("Couldn't find symbol entry for symbol(" + symbol + ")") ;
						} else {
							fLog.debug(ILogLevel.LEVEL_MID, String.format("Found doc item for class member %s",symbol)) ;
							symbolEntry.setDocPath(docFile.getDocPath()) ;
							symbolEntry.setDocumented(true) ;
						}
						break ;
					}
				}
			}
			if(ci.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt svdbVarDeclStmt = (SVDBVarDeclStmt)ci ;
				for(ISVDBChildItem child: svdbVarDeclStmt.getChildren()) {
					SVDBVarDeclItem varDeclItem = (SVDBVarDeclItem)child ;
					for(DocItem docItem: classDocItem.getChildren()) {
						if(docItem.getName().equals(varDeclItem.getName())) {
							docItem.setEnclosingClass(classDeclCacheItem.getName()) ;
							docItem.setEnclosingPkg(pkgDeclCacheItem.getName()) ;
							String symbol = docItem.getQualifiedName() ;
							SymbolTableEntry symbolEntry = fSymbolTable.getSymbol(symbol) ;
							if(symbolEntry == null) {
								fLog.error("Couldn't find symbol entry for symbol(" + symbol + ")") ;
							} else {
								fLog.debug(ILogLevel.LEVEL_MID, String.format("Found doc item for class member %s",symbol)) ;
								symbolEntry.setDocPath(docFile.getDocPath()) ;
								symbolEntry.setDocumented(true) ;
							}
							break ;
						}
					}
				}
			}

		}
	}

	private void indexClass(DocClassItem classItem, DocModel model) throws DocModelFactoryException {
		String name = classItem.getName() ;
		String firstChar = name.substring(0, 1).toUpperCase() ;
		Map<String, Map<String,DocItem>> classIndexMap = model.getCreateTopicIndexMap("class") ;
		if(classIndexMap.containsKey(firstChar)) {
			classIndexMap.get(firstChar)
				.put(name, classItem) ;
		} else if(firstChar.matches("[0123456789]")) {
			classIndexMap.get(DocModel.IndexKeyNum)
				.put(name,classItem) ;
		} else {
			classIndexMap.get(DocModel.IndexKeyWierd)
				.put(name,classItem) ;
		}
		
	}

}
