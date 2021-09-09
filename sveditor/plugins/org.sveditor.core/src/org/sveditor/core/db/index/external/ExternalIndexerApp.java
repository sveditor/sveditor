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
package org.sveditor.core.db.index.external;

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
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import org.sveditor.core.db.index.cache.file.SVDBFileSystem;
import org.sveditor.core.log.ILogHandle;
import org.sveditor.core.log.ILogListener;
import org.sveditor.core.log.LogFactory;

/**
 * - Need to break down the ArgFileIndex
 * -> Need to be able to perform operations 
 * @author ballance
 *
 */

public class ExternalIndexerApp {
	private SVDBFileSystem						fFS;
	
	public ExternalIndexerApp(File fs_path) {
		fFS = new SVDBFileSystem(fs_path, SVCorePlugin.getVersion());
	
		try {
			fFS.init();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	public void full_build() {
		
	}

	/**
	 * - Path to the cache filesystem
	 * - Server socket to connect to
	 * - Use special log message listener, so messages are channeled back to 'super'
	 * - Have 'super' setup initial filesystem
	 * -> Include paths
	 * -> Macro definitions
	 * -> List of files to parse
	 * - Have 'super' send build directives to 'sub'
	 * -> 
	 * -->  
	 * 
	 * - List of root files to parse
	 * - Directives (+define, +include, etc)
	 * - Filemap will need to be communicated in some form
	 * - Will want to commuicate some level of progress back
	 * - Path to cache file
	 * --> Upper level deals with argument files and path resolution
	 * --> External Indexer just processes SV files
	 * 
	 * There is an overhead to creating the persistence factory. 
	 * I'm uncertain what the overhead is. Perhaps, in the 
	 * grand scheme of things, the overhead isn't too bad.
	 * @param args
	 */
	public static final void main(String args[]) {
		long start, end;
		System.out.println("Hello World");
		String argfile = null;
		int port = -1;
		
		for (int i=0; i<args.length; i++) {
			if (args[i].charAt(0) == '-') {
				if (args[i].equals("-port")) {
					i++;
					try {
						port = Integer.parseInt(args[i]);
					} catch (NumberFormatException e) {
						e.printStackTrace();
					}
				} else {
					System.out.println("Error: Unknown option " + args[i]);
					System.exit(1);
				}
			} else {
				argfile = args[i];
			}
		}
		
		ExternalIndexerClient client = new ExternalIndexerClient();
		
		SVCorePlugin.testInit();
		LogFactory.getDefault().addLogListener(client);
//		SVCorePlugin.getDefault().enableDebug(false);
		
		try {
			client.connect(port);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
//		// Connect to the server in the IDE
//		Socket sock = null;
//		OutputStream os = null;
//		InputStream is = null;
//		try {
//			sock = new Socket();
////			sock.setReceiveBufferSize(1);
//			System.out.println("--> App: Connect " + port);
//			sock.connect(new InetSocketAddress(InetAddress.getLoopbackAddress(), port));
//			System.out.println("<-- App: Connect");
//			os = sock.getOutputStream();
//			is = sock.getInputStream();
//			
//			ExternalIndexerMsg msg = new ExternalIndexerMsg();
//			
//			System.out.println("--> App: write");
//			msg.write_str(ExternalIndexerMsgType.INIT_MSG.toString());
//			msg.send(os);
//			os.flush();
//			System.out.println("<-- App: write");
//
//			System.out.println("--> App: read");
//			msg.recv(is);
//			System.out.println("<-- App: read");
//			System.out.println("APP: c=" + msg.read_str());
//		} catch (IOException e) {
//			e.printStackTrace();
//		}

		
		client.run();

		System.exit(0); // client.run() should cause exit to be called
	}

}
