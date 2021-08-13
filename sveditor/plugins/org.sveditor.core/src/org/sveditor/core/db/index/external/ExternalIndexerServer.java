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

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexBuildData;

public class ExternalIndexerServer extends Thread {
	private ServerSocket				fServerSock;
	private Socket						fSocket;
	private InputStream					fIn;
	private OutputStream				fOut;
	private IProgressMonitor			fMonitor;
	private byte						fBuf[];
	private int							fBufSz;
	private int							fBufIdx;
	private List<ExternalIndexerMsg>	fMsgMailbox;
	private boolean						fIsAlive;
	
	public ExternalIndexerServer() throws IOException {
		fServerSock = new ServerSocket(0);
		fBuf = new byte[1024];
		fMsgMailbox = new ArrayList<ExternalIndexerMsg>();
	}
	
	public void setProgressMonitor(IProgressMonitor monitor) {
		fMonitor = monitor;
	}
	
	public int getListeningPort() {
		return fServerSock.getLocalPort();
	}

	public void connect() throws IOException {
		System.out.println("--> accept");
		fSocket = fServerSock.accept();
		System.out.println("<-- accept");
		
		try {
			fIn = fSocket.getInputStream();
			fOut = fSocket.getOutputStream();
		} catch (IOException e) { 
			e.printStackTrace();
		}
		fIsAlive = true;
		start();
	}
	
	public void shutdown() {
		synchronized (this) {
			fIsAlive = false;
		}
	}
	
	public void run() {
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
		ExternalIndexerMsg s_msg = new ExternalIndexerMsg();
	
//		s_msg.write_str(ExternalIndexerMsgType.INIT_MSG.toString());
//		try {
//			s_msg.send(fOut);
//			fOut.flush();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
		
		while (true) {
			try {
				msg.recv(fIn);
			} catch (IOException e) {
				System.out.println("Recv Thread: IOException");
				break;
			}
			
			if (!fIsAlive) {
				break;
			}
			
			String mt_s = msg.read_str();
			ExternalIndexerMsgType mt = ExternalIndexerMsgType.valueOf(mt_s);
			
			System.out.println("mt: " + mt);
			switch (mt) {
				case INDEX_RSP_MSG:
					synchronized (fMsgMailbox) {
						fMsgMailbox.add(msg);
						msg = new ExternalIndexerMsg();
						fMsgMailbox.notifyAll();
					}
					break;
				case DEBUG_MSG:
					System.out.println("Debug:");
					break;
			}
		}
	}
	
	public void send_exit_msg() {
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
	
		msg.write_str(ExternalIndexerMsgType.EXIT_MSG.toString());
		
		try {
			msg.send(fOut);
			fOut.flush();
		} catch (IOException e) { }
	}
	
	public void do_index(
			String						argfile,
			IProgressMonitor			monitor,
			SVDBArgFileIndexBuildData	build_data) {
		ExternalIndexerMsg msg = new ExternalIndexerMsg();
		msg.write_str(ExternalIndexerMsgType.INDEX_MSG.toString());
		msg.write_str(argfile);
	
		try {
			msg.send(fOut);
			fOut.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		ExternalIndexerMsg rsp = get_msg();
		System.out.println("Received index response");
	}

	private ExternalIndexerMsg get_msg() {
		ExternalIndexerMsg msg = null;
		
		do {
			synchronized (fMsgMailbox) {
				if (fMsgMailbox.size() > 0) {
					msg = fMsgMailbox.remove(0);
				}
			}
			
			if (msg == null) {
				synchronized (fMsgMailbox) {
					try {
						fMsgMailbox.wait();
					} catch (InterruptedException e) {
						break;
					}
				}
			}
		} while (msg == null);
		
		return msg;
	}
}
