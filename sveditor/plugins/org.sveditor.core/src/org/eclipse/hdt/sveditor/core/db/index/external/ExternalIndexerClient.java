/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.index.external;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.index.cache.file.SVDBFileSystem;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.ILogListener;

public class ExternalIndexerClient implements ILogListener {
	private Socket						fSock;
	private InputStream					fIn;
	private OutputStream				fOut;
	private List<ExternalIndexerMsg>	fMailbox;
	
	public ExternalIndexerClient() {
		fSock = new Socket();
		fMailbox = new ArrayList<ExternalIndexerMsg>();
	}
	
	public void connect(int port) throws IOException {
		fSock.connect(new InetSocketAddress(
				InetAddress.getLoopbackAddress(), port));
		fIn  = fSock.getInputStream();
		fOut = fSock.getOutputStream();
	}
	
	@Override
	public void message(ILogHandle handle, int type, int level, String message) {
//		System.out.println("MESSAGE: " + message);
		
		if (fOut != null) {
			synchronized (fOut) {
			
			}
		} else {
			// TODO: just print to stdout
		}
	}
	
	private static synchronized File createTempDir() {
		File tmpdir = new File(System.getProperty("java.io.tmpdir"));
		File ret = null; 
		
		for (int i=1; i<10000; i++) {
			File tmp = new File(tmpdir, "sveditor_tmp_" + i);
			if (!tmp.isDirectory()) {
				tmp.mkdirs();
				ret = tmp;
				break;
			}
		}
		
		return ret;
	}
	
	protected void build_index(String argfile) {
		File tmpdir = createTempDir();
		File db = new File(tmpdir, "db");
		SVDBFileSystem fs = new SVDBFileSystem(db, SVCorePlugin.getVersion());
		try {
			fs.init();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		// TODO: Need a special cache manager shell that always returns the target cache
		SVDBFileIndexCacheMgr cache_mgr = new SVDBFileIndexCacheMgr();
		cache_mgr.init(fs);
		
		
		ExternalIndexFilesystemProvider fs_provider = new ExternalIndexFilesystemProvider();
	
		String project = "GLOBAL";
		ISVDBIndex index = new SVDBArgFileIndex(
				project,
				argfile,
				fs_provider,
				cache_mgr.createIndexCache(project, argfile),
				null);

		index.init(new NullProgressMonitor(), null);
		
		long start, end;

		System.out.println("--> rebuild");
		start = System.currentTimeMillis();
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
//		index.rebuildIndex(new NullProgressMonitor());
		end = System.currentTimeMillis();
		System.out.println("<-- rebuild: " + (end-start));
		
		System.out.println("--> dispose");
		start = System.currentTimeMillis();
		cache_mgr.dispose();
		end = System.currentTimeMillis();
		System.out.println("<-- dispose: " + (end-start));
	}

	// Main loop for the client
	public void run() {
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
		
		while (true) {
			try {
				msg.recv(fIn);
			} catch (IOException e) {
				break;
			}
			
			String mt_s = msg.read_str();
			ExternalIndexerMsgType mt = ExternalIndexerMsgType.valueOf(mt_s);
			
			System.out.println("Client MT: " + mt);
	
			// Fork off as a thread so we can detect if the parent exits
			if (mt == ExternalIndexerMsgType.EXIT_MSG) {
				break;
			} else if (mt == ExternalIndexerMsgType.INDEX_MSG) {
				String argfile = msg.read_str();
				build_index(argfile);
				msg.init_write();
				msg.write_str(ExternalIndexerMsgType.INDEX_RSP_MSG.toString());
				
				try {
					msg.send(fOut);
					fOut.flush();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		
		try {
			fIn.close();
			fOut.close();
			fSock.close();
		} catch (IOException e) {
			
		}
		
		exit();
	}

	protected void exit() {
		System.exit(0);
	}
}
