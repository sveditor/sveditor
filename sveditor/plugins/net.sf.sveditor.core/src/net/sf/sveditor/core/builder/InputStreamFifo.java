package net.sf.sveditor.core.builder;

import java.io.IOException;
import java.io.InputStream;

public class InputStreamFifo extends InputStream {
	int						head;
	int						tail;
	int						fQueueSize = 4096;
	int						fNumElems;
	char					fQueue[] = new char[fQueueSize];
	boolean					fClosed;
	
	public InputStreamFifo() {
	}

	@Override
	public int read() throws IOException {
		int ret = -1;
		while (true) {
			synchronized (fQueue) {
				if (fNumElems != 0) {
					ret = fQueue[tail];
					tail = (tail + 1) % fQueueSize;
					fNumElems--;
					fQueue.notifyAll();
					break;
				} else {
					if (fClosed) {
						break;
					} else {
						try {
							fQueue.wait();
						} catch (InterruptedException e) {
							break;
						}
					}
				}
			}
		}
		
		return ret;
	}
	
	public void write(String msg) {
		synchronized (fQueue) {
			for (int i=0; i<msg.length(); i++) {
				while (fNumElems == fQueueSize) {
					fQueue.notifyAll();
					// Wait for the queue to empty
					try {
						fQueue.wait();
					} catch (InterruptedException e) { }
				}
				fQueue[head] = msg.charAt(i);
				head = (head + 1) % fQueueSize;
				fNumElems++;
			}
			fQueue.notifyAll();
		}
	}
	
	public void end() {
		fClosed = true;
		synchronized (fQueue) {
			fQueue.notifyAll();
		}
	}
	
	public void waitFor() {
		while (true) {
			synchronized (fQueue) {
				if (fNumElems == 0) {
					break;
				} else {
					try {
						fQueue.wait();
					} catch (InterruptedException e) {
						break;
					}
				}
			}
		}
	}
	
	public boolean active() {
		synchronized (fQueue) {
			return (!fClosed || fNumElems > 0);
		}
	}

}
