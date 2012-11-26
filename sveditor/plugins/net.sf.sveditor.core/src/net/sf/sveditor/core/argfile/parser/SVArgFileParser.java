package net.sf.sveditor.core.argfile.parser;

import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.argfile.parser.ISVArgFileOptionProvider.OptionType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.argfile.SVDBArgFileDefineStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncDirStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFileIncFileStmt;
import net.sf.sveditor.core.db.argfile.SVDBArgFilePathStmt;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;

public class SVArgFileParser {
	private SVArgFileOptionProviderList			fOptionProviders;
	private SVArgFileLexer						fLexer;
	private String								fFilename;
	private LogHandle							fLog;
	private boolean							fDebugEn = true;
	private List<SVDBMarker>					fMarkers;
	private ISVDBFileSystemProvider				fFSProvider;
	
	public SVArgFileParser(ISVDBFileSystemProvider fs_provider) {
		fOptionProviders = new SVArgFileOptionProviderList();
		fOptionProviders.add(new SVArgFileQuestaOptionProvider());
		fOptionProviders.add(new SVArgFileVCSOptionProvider());
		fOptionProviders.add(new SVArgFileNCVlogOptionProvider());
		
		fLog = LogFactory.getLogHandle("SVArgFileParser");
		fFSProvider = fs_provider;
	}
	
	public void init(SVArgFileLexer lexer, String name) {
		fLexer = lexer;
		fFilename = name;
	}
	
	public SVDBFile parse(
			SVDBFile			file,
			List<SVDBMarker> 	markers) throws SVParseException {
		
		fMarkers = markers;
	
		if (fDebugEn) {
			fLog.debug("--> parse() " + fFilename);
		}
		
		while (fLexer.peek() != null) {
			if (fLexer.isOption()) {
				SVArgFileToken tok = fLexer.consumeToken();
				OptionType type = fOptionProviders.getOptionType(tok.getImage());
				int arg_count = fOptionProviders.optionArgCount(tok.getImage());
				
				if (fDebugEn) {
					fLog.debug("  isOption: " + tok.getImage() + " type=" + type + 
							" arg_count=" + arg_count);
				}
				
				// Determine what type of option this is
				switch (type) {
					case Unrecognized: {
						// TODO: Treat as a single-item option and ignore
						fLexer.eatToken();
						} break;
					
						// Recognized, but ignored, option
					case Ignored: {
						// TODO: Consume known options
						for (int i=0; i<arg_count; i++) {
							fLexer.eatToken();
						}
						} break;
						
					case Incdir: {
						SVDBArgFileIncDirStmt stmt = new SVDBArgFileIncDirStmt();
						stmt.setLocation(fLexer.getStartLocation());
						String path;
						
						if (arg_count > 0) {
							// include path is the argument
							path = fLexer.readPath();
							List<String> inc_path_l = fOptionProviders.getIncPaths(tok.getImage(), path);
							path = inc_path_l.get(0);
						} else {
							List<String> inc_path_l = fOptionProviders.getIncPaths(
									tok.getImage(), 
									tok.getOptionVal());
							path = inc_path_l.get(0);
						}
					
						path = resolvePath(path);
						
						if (!fFSProvider.fileExists(path)) {
							error("Include path \"" + path + "\" does not exist");
						}
						stmt.setIncludePath(path);
						
						file.addChildItem(stmt);
						} break;
						
					case Define: {
						SVDBArgFileDefineStmt stmt = new SVDBArgFileDefineStmt();
						stmt.setLocation(fLexer.getStartLocation());
						Tuple<String, String> def;
						
						if  (arg_count > 0) {
							// Define is the argument
							def = fOptionProviders.getDefValue(
									tok.getImage(),
									fLexer.readPath());
						} else {
							def = fOptionProviders.getDefValue(
									tok.getImage(),
									tok.getOptionVal());
						}
						
						stmt.setKey(def.first());
						stmt.setValue(def.second());
						
						file.addChildItem(stmt);
						} break;
						
					case ArgFileInc: {
						SVDBArgFileIncFileStmt stmt = new SVDBArgFileIncFileStmt();
						stmt.setLocation(tok.getStartLocation());
						List<String> incs;
						
						if (arg_count > 0) {
							incs = fOptionProviders.getArgFilePaths(
									tok.getImage(), fLexer.readPath());
						} else {
							incs = fOptionProviders.getArgFilePaths(
									tok.getImage(),
									tok.getOptionVal());
						}
						
						if (incs == null || incs.size() == 0) {
							error("No argument-file path provided");
						} else {
							String inc = incs.get(0);
							System.out.println("Inc: " + inc + " len=" + incs.size());
							String path = resolvePath(incs.get(0));
							if (!fFSProvider.fileExists(path)) {
								error("Argument-file path \"" + path + "\" does not exist");
							}
							stmt.setPath(path);
							file.addChildItem(stmt);
						}
						} break;
						
					default:
						error("Unrecognized option type " + type);
						break;
				}
			} else {
				// It's a path
				SVDBArgFilePathStmt p = new SVDBArgFilePathStmt();
				p.setLocation(fLexer.getStartLocation());
				p.setPath(fLexer.eatToken());
				file.addChildItem(p);
				
				// Try to resolve path
				String path = resolvePath(p.getPath());
				
				if (!fFSProvider.fileExists(path)) {
					error("Path \"" + path + "\" does not exist");
				}
			}
		}
		
		fLog.debug("<-- parse() " + fFilename);
		
		return file;
	}
	
	private String resolvePath(String path) {
		for (String fmt : new String[] { null,
				ISVDBFileSystemProvider.PATHFMT_WORKSPACE,
				ISVDBFileSystemProvider.PATHFMT_FILESYSTEM}) {
			String rpath = fFSProvider.resolvePath(path, fmt);
			
			if (fFSProvider.fileExists(rpath)) {
				path = rpath;
				break;
			}
		}
	
		return path;
	}
	
	private void error(String msg) throws SVParseException {
		if (fMarkers != null) {
			SVDBMarker m = new SVDBMarker(MarkerType.Error, MarkerKind.UndefinedMacro, msg);
			m.setLocation(fLexer.getStartLocation());
			fMarkers.add(m);
		}
		System.out.println("[ERROR] " + msg);
	}
}
