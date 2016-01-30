package net.sf.sveditor.core.db.index.external;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;

import org.eclipse.core.runtime.IProgressMonitor;

public class ExternalIndexerServer extends Thread {
	private ServerSocket				fServerSock;
	private Socket						fSocket;
	private InputStream					fIn;
	private IProgressMonitor			fMonitor;
	private byte						fBuf[];
	private int							fBufSz;
	private int							fBufIdx;
	
	public ExternalIndexerServer() throws IOException {
		fServerSock = new ServerSocket(0);
		fBuf = new byte[1024];
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
		start();
	}

	public void run() {
		try {
			fIn = fSocket.getInputStream();
			OutputStream os = fSocket.getOutputStream();
			System.out.println("--> write");
			os.write('B');
			os.flush();
			System.out.println("<-- write");
		} catch (IOException e) { }

		int c = getch();
		
		System.out.println("c=" + c);
	}

	private int getch() {
		int ret = -1;
		
		if (fBufIdx >= fBufSz) {
			fBufIdx = 0;
			fBufSz = 0;
			try {
				fBufSz = fIn.read(fBuf, 0, fBuf.length);
			} catch (IOException e) {}
		}
		
		if (fBufIdx < fBufSz) {
			ret = fBuf[fBufIdx++];
		}
		
		return ret;
	}
}
