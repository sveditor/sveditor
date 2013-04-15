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

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

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
import net.sf.sveditor.core.docs.DocCommentCleaner;
import net.sf.sveditor.core.docs.DocCommentParser;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.DocKeywordInfo;
import net.sf.sveditor.core.docs.DocTopicType;
import net.sf.sveditor.core.docs.IDocCommentParser;
import net.sf.sveditor.core.docs.IDocTopicManager;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;


/**
 * Factory which produces a DocModel for a given DocGenConfig
 * <p>
 * @see DocModel
 * @see DocGenConfig
 */
public class DocModelFactory {
	
	private LogHandle fLog ;
	
	private class DocModelFactoryException extends Exception {
		private static final long serialVersionUID = -6656720421849741060L;
		public DocModelFactoryException(String msg) {
			super(msg) ;
		}
	}
	
	public DocModelFactory() {
		fLog = LogFactory.getLogHandle("DocModelFactory") ;
	}

	/**
	 * @param cfg Configuration defining the set to be generated.
	 * @return A fully prepared DocModel indexed and cross referenced
	 */
	public DocModel build(DocGenConfig cfg) {
		DocModel model = new DocModel() ;
		IDocCommentParser docCommentParser = new DocCommentParser(model.getDocTopics()) ;
		try {
			gatherSymbols(cfg, model) ;
			gatherDocTopicsFromPreProcFiles(cfg, model, docCommentParser) ;
			gatherPackageContentFromDeclCache(cfg, model) ;
			assignSymbolsTheirDocFiles(cfg, model) ;
			setPageTitles(cfg, model) ;
			indexTopics(cfg,model) ;
		} catch (Exception e) {
			fLog.error("Document model build failed: " + e.toString(), e);
		}
		return model ;
	}

	/**
	 * @param cfg Configuration to operate within
	 * @param model The model to operate on
	 */
	private void assignSymbolsTheirDocFiles(DocGenConfig cfg, DocModel model) {
		for(String symbol: model.getSymbolTable().getSymbolSet()) {
			SymbolTableEntry entry = model.getSymbolTable().getSymbol(symbol) ;
			String file = entry.getFile() ;
			DocFile docFile = model.getDocFile(file) ;
			if(docFile == null) {
				fLog.debug(ILogLevel.LEVEL_MIN,
						String.format("Failed to find docFile for symbol(%s)", symbol)) ;
			} else {
				fLog.debug(ILogLevel.LEVEL_MID,
						String.format("Found symbol's(%s) docFile(%s)",
								symbol,
								file)) ;
				entry.setDocFile(docFile) ;
			}
		}
	}

	/**
	 * @param cfg Configuration to operate within
	 * @param model The model to operate on
	 */
	private void setPageTitles(DocGenConfig cfg, DocModel model) {
		// If the first topic in the file has the "page title if first" attribute set,
		// then use that as the title. Otherwise, just use the file name
		IDocTopicManager topicMgr = model.getDocTopics() ;
		for(DocFile docFile: model.getDocFiles()) {
			boolean setFromTopic = false ;
			for(DocTopic childTopic: docFile.getChildren()) {
				DocKeywordInfo kwi = topicMgr.getTopicType(childTopic.getKeyword()) ;
				if(kwi.getTopicType().isPageTitleIfFirst()) {
					docFile.setPageTitle(childTopic.getTitle()) ;
					setFromTopic = true ;
				} 
				break ;
			}
			if(!setFromTopic){
				File file = new File(docFile.getTitle()) ;
				docFile.setPageTitle(file.getName()) ;
			}
		}
	}

	/**
	 * Creates the first-pass model purely from DocTopics parsed from
	 * the preprocessor view of each source file.
	 * <p><p>
	 * After this step:
	 * <ul>
	 * <li> The model has a DocFile for each preprocessor file which contains any DocTopic
	 * <li> Each DocFile has a set of all DocTopics parsed from the raw doc comments found in the file
	 * </ul>
	 * <p>
	 * @param cfg Configuration to operate within
	 * @param model The model to operate on
	 * @param docCommentParser
	 */
	private void gatherDocTopicsFromPreProcFiles(DocGenConfig cfg, DocModel model, IDocCommentParser docCommentParser) {
		HashSet<ISVDBIndex> visitedIndex = new HashSet<ISVDBIndex>() ;
		fLog.debug(ILogLevel.LEVEL_MIN,"Gathering raw doc comments for each SVDBFile") ;
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> pkgTuple: cfg.getSelectedPackages()) {
			ISVDBIndex index = pkgTuple.second() ;
			if(!visitedIndex.contains(index)) {
				visitedIndex.add(index) ;
				for(String file: index.getFileList(new NullProgressMonitor())) {
					DocTopic parent = null ;
//					SVDBFile ppFile = index.getCache().getPreProcFile(new NullProgressMonitor(), file) ;
					SVDBFile ppFile = index.findPreProcFile(new NullProgressMonitor(), file);
					if(ppFile == null) {
						fLog.error("Failed to find pre proc file for: " + file) ;
					} else {
						fLog.debug(ILogLevel.LEVEL_MID,"+-------------------------------------------------------------------------------") ;
						fLog.debug(ILogLevel.LEVEL_MID,"| Entering file(" + file + ")") ;
						fLog.debug(ILogLevel.LEVEL_MID,"+-------------------------------------------------------------------------------") ;
						String path = file ;
						String shortFileName = new File(path).getName() ;
						if (path.startsWith("${workspace_loc}")) {
							path = path.substring("${workspace_loc}".length()) ;
						}
						DocFile docFile = new DocFile(file) ;
						parent = docFile ;
						docFile.setDocPath(path) ;
						boolean fileHasDocs = false ;
						for(ISVDBChildItem child: ppFile.getChildren()) {
							if(child instanceof SVDBDocComment) {
								List<DocTopic> docTopics = new ArrayList<DocTopic>() ; 
								SVDBDocComment docCom = (SVDBDocComment)child ;
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] +------------------------------------------------------------------------------------",
												shortFileName)) ;
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] | Parsing comment: %s",
												shortFileName,
												docCom.getName())) ;
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] | +------------------------------------------------------------------------------------",
												shortFileName)) ;
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] | | Body:",
												shortFileName)) ;
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] | +------------------------------------------------------------------------------------",
												shortFileName)) ;
								String lines[] = DocCommentCleaner.splitCommentIntoLines(docCom.getRawComment()) ;
								int lin_num=0 ;
								for(String line: lines) {
									fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] | | [%03d]: %s",
												shortFileName,
												lin_num,
												line)) ;
									lin_num++ ;
								}
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] | +------------------------------------------------------------------------------------",
												shortFileName)) ;
								docCommentParser.parse(docCom.getRawComment(),docTopics) ;
								for(DocTopic topic: docTopics) {
									IDocTopicManager topicMgr = model.getDocTopics() ;
									DocKeywordInfo kwi = topicMgr.getTopicType(topic.getKeyword()) ;
									// FIXME: check kwi != null
									fLog.debug(ILogLevel.LEVEL_MID,
											String.format("| [%s] |    Found topic: %s",
													shortFileName,
													topic.getTitle())) ;
									fLog.debug(ILogLevel.LEVEL_MID,
											String.format("| [%s] |      	summary: %s",
													shortFileName,
													topic.getSummary())) ;
									fileHasDocs = true ;
									switch(kwi.getTopicType().getScopeType()) {
										case START:
											docFile.addChild(topic) ;
											parent = topic ;
											break ;
										case NORMAL:
											parent.addChild(topic) ;
											break ;
										case END:
											parent = docFile ;
											parent.addChild(topic) ;
											break ;
										default:
											break ;
									}
								}
								fLog.debug(ILogLevel.LEVEL_MID,
										String.format("| [%s] +------------------------------------------------------------------------------------",
												shortFileName)) ;
							}
						}						
						fLog.debug(ILogLevel.LEVEL_MID,"+-------------------------------------------------------------------------------") ;
						fLog.debug(ILogLevel.LEVEL_MID,"| Exiting file(" + file + ")") ;
						fLog.debug(ILogLevel.LEVEL_MID,"+-------------------------------------------------------------------------------") ;
						if(fileHasDocs) {
							model.addDocFile(docFile) ;
						}
					}
				}
			}
		}
	}

	/**
	 * Populates the model's initial symbol table by gathering symbols 
	 * from the declaration cache for all packages selected by the given configuration.
	 * <p><p>
	 * After this pass:
	 * <ul>
	 * </ul>
	 * @param cfg Configuration to operate within
	 * @param model The model to operate on
	 * @see SymbolTableEntry
	 * @see SymbolTable
	 * 
	 */
	private void gatherSymbols(DocGenConfig cfg, DocModel model) {
		
		fLog.debug(ILogLevel.LEVEL_MIN,"Building initial symbol table the SVDB") ;
		
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> pkgTuple: cfg.getSelectedPackages()) {
			SVDBDeclCacheItem pkgDeclCacheItem = pkgTuple.first() ;
			ISVDBIndex pkgSvdbIndex = pkgTuple.second() ;
			SymbolTableEntry pkgSTE = 
					SymbolTableEntry.createPkgEntry(pkgDeclCacheItem.getName(), pkgSvdbIndex, pkgDeclCacheItem.getFilename(), pkgDeclCacheItem) ;
			model.getSymbolTable().addSymbol(pkgSTE) ;
			gatherSymbolsFromPackage(cfg, model, pkgDeclCacheItem, pkgSvdbIndex) ;
		}
		model.getSymbolTable().dumpSymbols() ;
		
	}

	private void gatherSymbolsFromPackage(DocGenConfig cfg, 
										DocModel model, 
										SVDBDeclCacheItem pkgDeclCacheItem, 
										ISVDBIndex pkgSvdbIndex) {
		
		List<SVDBDeclCacheItem> pkgDecls = pkgDeclCacheItem.getParent().findPackageDecl(new NullProgressMonitor(), pkgDeclCacheItem) ; 
		if(pkgDecls != null) {
			for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
				if(pkgDecl.getType() == SVDBItemType.ClassDecl) {
					SymbolTableEntry classSTE = 
							SymbolTableEntry.createClassEntry(pkgDeclCacheItem.getName(), pkgDecl.getName(), pkgSvdbIndex, pkgDecl.getFilename(), pkgDecl) ;
					model.getSymbolTable().addSymbol(classSTE) ;
					gatherSymbolsFromClass(cfg,model,pkgSvdbIndex,pkgDeclCacheItem,pkgDecl) ;
				}
			}
		} else {
			fLog.debug(ILogLevel.LEVEL_MID,"No decls found for pkg(" + pkgDeclCacheItem.getName() + ")") ;
		}
	}
			

	private void gatherSymbolsFromClass(DocGenConfig cfg, DocModel model,
			ISVDBIndex pkgSvdbIndex, SVDBDeclCacheItem pkgDeclCacheItem,
			SVDBDeclCacheItem classDeclCacheItem) {
		
		SVDBClassDecl svdbClassDecl = (SVDBClassDecl)classDeclCacheItem.getSVDBItem() ;
		if (svdbClassDecl == null) {
			fLog.error("DocModelFactory Failed to obtain cache handle for " + 
					classDeclCacheItem.getName());
		}
		for(ISVDBChildItem ci: svdbClassDecl.getChildren()) {
			if(ci.getType() == SVDBItemType.Task) {
				SVDBTask svdbTask = (SVDBTask)ci ;
				SymbolTableEntry taskSTE =
						SymbolTableEntry.createClassMemberEntry(pkgDeclCacheItem.getName(), 
								classDeclCacheItem.getName(), 
								svdbTask.getName(), 
								pkgSvdbIndex,
								classDeclCacheItem.getFilename()) ;
				model.getSymbolTable().addSymbol(taskSTE) ;
			} else if(ci.getType() == SVDBItemType.Function) {
				SVDBFunction svdbFunction = (SVDBFunction)ci ;
				SymbolTableEntry funcSTE =
						SymbolTableEntry.createClassMemberEntry(pkgDeclCacheItem.getName(), 
								classDeclCacheItem.getName(), 
								svdbFunction.getName(), 
								pkgSvdbIndex,
								classDeclCacheItem.getFilename()) ;
				model.getSymbolTable().addSymbol(funcSTE) ;
			} else if(ci.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt varDecl = (SVDBVarDeclStmt)ci ;
				for(ISVDBChildItem varItem: varDecl.getChildren()) {
					if(varItem instanceof SVDBVarDeclItem) {
						SVDBVarDeclItem varDeclItem = (SVDBVarDeclItem)varItem ;
						SymbolTableEntry varSTE =
								SymbolTableEntry.createClassMemberEntry(pkgDeclCacheItem.getName(), 
										classDeclCacheItem.getName(), 
										varDeclItem.getName(), 
										pkgSvdbIndex,
										classDeclCacheItem.getFilename()) ;
						model.getSymbolTable().addSymbol(varSTE) ;
					}
				}
			}
		}		
		
	}
	
	/**
	 * Compliments the first-pass DocTopic based model with the more detailed
	 * information available from the SVDBDeclCacheItems and the SVDB itself.
	 * <p><p>
	 * Specifically:
	 * <ul>
	 * <li>
	 * </ul>
	 * <p>
	 * @param cfg
	 * @param model
	 * @throws DocModelFactoryException
	 */
	private void gatherPackageContentFromDeclCache(DocGenConfig cfg, DocModel model) throws DocModelFactoryException {
		fLog.debug(ILogLevel.LEVEL_MIN,
				"Iterating through SVDB to compliment Doc Comments") ;
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> pkgTuple: cfg.getSelectedPackages()) {
			SVDBDeclCacheItem pkg = pkgTuple.first() ;
			if(pkg.getParent() == null) {
				throw new DocModelFactoryException("Package had no parent index: " + pkg.getName()) ;
			}
			gatherPackageClasses(model, pkg, pkgTuple.second());			
		}
	}

	private void gatherPackageClasses(DocModel model, 
									  SVDBDeclCacheItem pkg,
									  ISVDBIndex isvdbIndex)
			throws DocModelFactoryException {
		String pkgName = pkg.getName() ;
		fLog.debug(ILogLevel.LEVEL_MID,"+------------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_MID,"| Entering package: " + pkgName) ;
		fLog.debug(ILogLevel.LEVEL_MID,"+------------------------------------------------------------") ;
		/*
		 * Request, from the decl cache, all declarations within the given package and iterate over them
		 */
		List<SVDBDeclCacheItem> pkgDecls = pkg.getParent().findPackageDecl(new NullProgressMonitor(), pkg) ; 
		if(pkgDecls != null) {
			for(SVDBDeclCacheItem pkgDecl: pkgDecls) {
				/*
				 * For each decl cache item, search for an associate doc comment in the preprocessor
				 * view of the file the item was declared in.
				 */
//				SVDBFile ppFile = isvdbIndex.getCache().getPreProcFile(new NullProgressMonitor(), pkgDecl.getFile().getFilePath()) ;
				SVDBFile ppFile = isvdbIndex.findPreProcFile(new NullProgressMonitor(), pkgDecl.getFile().getFilePath()) ;
				if(ppFile != null) {
					String symbol = String.format("%s::%s", pkg.getName(), pkgDecl.getName()) ;
					DocFile docFile = model.getDocFile(pkgDecl.getFile().getFilePath()) ;
					if(docFile != null) {
						for(DocTopic docItem: docFile.getChildren()) {
							if(docItem.getTitle().equals(pkgDecl.getName())) {
								fLog.debug(ILogLevel.LEVEL_MID, 
										String.format("| [%s] Found doc comment for: %s", pkgName, symbol)) ;
								SymbolTableEntry symbolEntry = model.getSymbolTable().getSymbol(symbol) ;
								if(symbolEntry == null) {
									fLog.debug(ILogLevel.LEVEL_MIN,
											"Couldn't find symbol entry for symbol(" + symbol + ")") ;
								} else {
									symbolEntry.setDocFile(docFile) ;
									symbolEntry.setDocumented(true) ;
									docItem.setEnclosingPkg(pkg.getName()) ;
									if(pkgDecl.getType() == SVDBItemType.ClassDecl && docItem.getTopic().equals("class")) {
										gatherClassMembers(docItem, pkg, pkgDecl, model, isvdbIndex, docFile, ppFile) ;
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
	
	private void gatherClassMembers(DocTopic classDocItem, 
									SVDBDeclCacheItem pkgDeclCacheItem, 
									SVDBDeclCacheItem classDeclCacheItem, 
									DocModel model, 
									ISVDBIndex isvdbIndex,
									DocFile docFile,
									SVDBFile ppFile ) {
		SVDBClassDecl svdbClassDecl = (SVDBClassDecl)classDeclCacheItem.getSVDBItem() ;
		String pkgName = pkgDeclCacheItem.getName() ;
		String className = svdbClassDecl.getName() ;
		fLog.debug(ILogLevel.LEVEL_MID,
				String.format("| [%s] +------------------------------------------------------------",
						pkgName)) ;
		fLog.debug(ILogLevel.LEVEL_MID,
				String.format("| [%s] | Entering class: %s",
						pkgName, 
						className)) ;
		fLog.debug(ILogLevel.LEVEL_MID,
				String.format("| [%s] +------------------------------------------------------------",
						pkgName)) ;
		for(ISVDBChildItem ci: svdbClassDecl.getChildren()) {
			if(ci.getType() == SVDBItemType.Task) {
				SVDBTask svdbTask = (SVDBTask)ci ;
				for(DocTopic docItem: classDocItem.getChildren()) {
					if(docItem.getTitle().equals(svdbTask.getName())) {
						docItem.setEnclosingClass(classDeclCacheItem.getName()) ;
						docItem.setEnclosingPkg(pkgDeclCacheItem.getName()) ;
						String symbol = docItem.getQualifiedName() ;
						SymbolTableEntry symbolEntry = model.getSymbolTable().getSymbol(symbol) ;
						if(symbolEntry == null) {
							fLog.debug(ILogLevel.LEVEL_MIN,
									"Couldn't find symbol entry for symbol(" + symbol + ")") ;
						} else {
							fLog.debug(ILogLevel.LEVEL_MID, 
									String.format("| [%s] | [%s] Found doc item for task %s",
											pkgName, 
											className, 
											symbol)) ;
							symbolEntry.setDocFile(docFile) ;
							symbolEntry.setDocumented(true) ;
						}
						break ;
					}
				}
			}
			if(ci.getType() == SVDBItemType.Function) {
				SVDBFunction svdbFunc = (SVDBFunction)ci ;
				for(DocTopic docItem: classDocItem.getChildren()) {
					if(docItem.getTitle().equals(svdbFunc.getName())) {
						docItem.setEnclosingClass(classDeclCacheItem.getName()) ;
						docItem.setEnclosingPkg(pkgDeclCacheItem.getName()) ;
						String symbol = docItem.getQualifiedName() ;
						SymbolTableEntry symbolEntry = model.getSymbolTable().getSymbol(symbol) ;
						if(symbolEntry == null) {
							fLog.debug(ILogLevel.LEVEL_MIN,
									"Couldn't find symbol entry for symbol(" + symbol + ")") ;
						} else {
							fLog.debug(ILogLevel.LEVEL_MID, 
									String.format("| [%s] | [%s] Found doc item for function %s",
											pkgName, 
											className, 
											symbol)) ;
							symbolEntry.setDocFile(docFile) ;
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
					for(DocTopic docItem: classDocItem.getChildren()) {
						if(docItem.getTitle().equals(varDeclItem.getName())) {
							docItem.setEnclosingClass(classDeclCacheItem.getName()) ;
							docItem.setEnclosingPkg(pkgDeclCacheItem.getName()) ;
							String symbol = docItem.getQualifiedName() ;
							SymbolTableEntry symbolEntry = model.getSymbolTable().getSymbol(symbol) ;
							if(symbolEntry == null) {
								fLog.debug( ILogLevel.LEVEL_MIN,
										"Couldn't find symbol entry for symbol(" + symbol + ")") ;
							} else {
								fLog.debug(ILogLevel.LEVEL_MID, 
										String.format("| [%s] | [%s] Found doc item for var %s",
												pkgName, 
												className, 
												symbol)) ;
								symbolEntry.setDocFile(docFile) ;
								symbolEntry.setDocumented(true) ;
							}
							break ;
						}
					}
				}
			}
		}
		fLog.debug(ILogLevel.LEVEL_MID,
				String.format("| [%s] +------------------------------------------------------------",
						pkgName)) ;
	}
	
	private void indexTopics(DocGenConfig cfg, DocModel model) {
		// 
		IDocTopicManager dtMan = model.getDocTopics() ;
		for(DocTopicType docTopicType: dtMan.getAllTopicTypes()) {
			if(docTopicType.isIndex()) {
				model.getCreateTopicIndexMap(docTopicType.getName()) ;
			}
		}
		//
		for(DocTopic item: model.getDocFiles()) {
		  indexTopic(model, item);
		}
	}

	private void indexTopic(DocModel model, DocTopic item) {
		DocIndex docIndex = model.getTopicIndexMap(item.getTopic().toLowerCase()) ;	
		if(docIndex != null) {
			docIndex.indexTopic(item) ; 
		}
		for(DocTopic child: item.getChildren()) {
			indexTopic(model,child) ;
		}
	}
	
}
