package net.sf.sveditor.core.tests.index.argfile2;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBIndexChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestFileChangeBase extends SVCoreTestCaseBase {

	private List<Integer>		fEvents = new ArrayList<Integer>();
	private List<Integer>		fIndexChangeEvents = new ArrayList<Integer>();
	private List<ISVDBIndex>	fRegisteredIndexes = new ArrayList<ISVDBIndex>();
	private Object				fSharedEvent = new Object();
	
	IResourceChangeListener 	fListener = new IResourceChangeListener() {
		
		@Override
		public void resourceChanged(IResourceChangeEvent event) {
			synchronized (fEvents) {
				fEvents.add(1);
				fEvents.notifyAll();
			}
			synchronized (fSharedEvent) {
				fSharedEvent.notifyAll();
			}
		}
	};
	
	ISVDBIndexChangeListener 	fIndexChangeListener = new ISVDBIndexChangeListener() {
		@Override
		public void index_event(SVDBIndexChangeEvent e) {
			fLog.debug("index_event: " + e.getType() + " index: " + e.getIndex());
			synchronized (fIndexChangeEvents) {
				fIndexChangeEvents.add(1);
				fIndexChangeEvents.notifyAll();
			}
			synchronized (fSharedEvent) {
				fSharedEvent.notifyAll();
			}			
		}
	};
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(fListener);
	}

	@Override
	protected void tearDown() throws Exception {
		waitIndexEvent(100); // Just wait for a bit
		
		super.tearDown();
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(fListener);
		
		for (ISVDBIndex i : fRegisteredIndexes) {
			i.removeChangeListener(fIndexChangeListener);
		}
		fRegisteredIndexes.clear();
	}
	
	protected void addIndex(ISVDBIndex i) {
		fRegisteredIndexes.add(i);
		i.addChangeListener(fIndexChangeListener);
	}
	
	protected void addIndex(SVDBIndexCollection i) {
		for (ISVDBIndex ii : i.getIndexList()) {
			addIndex(ii);
		}
	}
	
	protected void clearEvents() {
		synchronized (fEvents) {
			fEvents.clear();
		}
	}
	
	protected boolean waitEvent() {
		return waitEvent(10000);
	}
	
	protected boolean waitEvent(int timeout) {
		boolean ret = false;
		
		synchronized (fEvents) {
			ret = (fEvents.size() > 0);
			fEvents.clear();
		}
		
		if (!ret) {
			try {
				synchronized (fEvents) {
					fEvents.wait(timeout);
					ret = (fEvents.size() > 0);
					fEvents.clear();
				}
			} catch (InterruptedException e) { }
		}

		return ret;
	}

	protected boolean waitIndexEvent(int timeout) {
		boolean ret = false;
		
		synchronized (fIndexChangeEvents) {
			ret = (fIndexChangeEvents.size() > 0);
			fIndexChangeEvents.clear();
		}
		
		if (ret) {
			fLog.debug("Note: early exit from waitIndexEvent");
			synchronized (fEvents){
				fEvents.clear();
			}
			return ret;
		}
		
		synchronized (fIndexChangeEvents) {
			try {
				fIndexChangeEvents.wait(timeout);
			} catch (InterruptedException e) {
				System.out.println("Interrupted");
			}
			ret = (fIndexChangeEvents.size() > 0);
			fIndexChangeEvents.clear();
		}
		synchronized (fEvents){
			fEvents.clear();
		}
		
		fLog.debug("Note: normal exit from waitIndexEvent: " + ret);
	
		return ret;
	}
	
	protected boolean waitIndexEvent() {
		return waitIndexEvent(20000);
	}
	
}
