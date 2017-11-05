package net.sf.sveditor.ui.console;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.IStreamListener;
import org.eclipse.debug.core.model.IFlushableStreamMonitor;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.debug.internal.ui.DebugUIPlugin;
import org.eclipse.debug.internal.ui.preferences.IDebugPreferenceConstants;
import org.eclipse.debug.internal.ui.views.console.ConsoleLineNotifier;
import org.eclipse.debug.internal.ui.views.console.ProcessConsoleManager;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.console.ConsoleColorProvider;
import org.eclipse.debug.ui.console.IConsole;
import org.eclipse.debug.ui.console.IConsoleColorProvider;
import org.eclipse.debug.ui.console.IConsoleHyperlink;
import org.eclipse.debug.ui.console.IConsoleLineTracker;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IRegion;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IHyperlink;
import org.eclipse.ui.console.IOConsole;
import org.eclipse.ui.console.IOConsoleOutputStream;

import com.ibm.icu.text.MessageFormat;
import com.sun.org.apache.bcel.internal.generic.FMUL;

public class SVConsole extends IOConsole implements IConsole {

	protected SVConsoleManager			fConsoleMgr;
    protected IConsoleColorProvider 	fColorProvider;
    private boolean 					fAllocateConsole = true;
    protected IStreamsProxy				fStreamsProxy;
    
	private List<StreamListener> 		fStreamListeners = new ArrayList<StreamListener>();
    
    protected SVConsole(
    		SVConsoleManager	mgr,
    		String				name,
    		String				type,
    		ImageDescriptor		img) {
    	super(name, img);
    	fConsoleMgr = mgr;
    	
        IConsoleLineTracker[] lineTrackers = fConsoleMgr.getLineTrackers(type);
        if (lineTrackers.length > 0) {
        	SVConsoleLineNotifier notifier = new SVConsoleLineNotifier(lineTrackers);
        	notifier.connect(this);
            addPatternMatchListener(notifier);
        }    	
    }
    
    public IStreamsProxy getStreamsProxy() {
    	return fStreamsProxy;
    }
    
	@Override
	public void connect(IStreamsProxy streamsProxy) {
        IPreferenceStore store = DebugUIPlugin.getDefault().getPreferenceStore();
        IStreamMonitor streamMonitor = streamsProxy.getErrorStreamMonitor();
        if (streamMonitor != null) {
            connect(streamMonitor, IDebugUIConstants.ID_STANDARD_ERROR_STREAM,
            		store.getBoolean(IDebugPreferenceConstants.CONSOLE_OPEN_ON_ERR));
        }
        streamMonitor = streamsProxy.getOutputStreamMonitor();
        if (streamMonitor != null) {
            connect(streamMonitor, IDebugUIConstants.ID_STANDARD_OUTPUT_STREAM, 
            		store.getBoolean(IDebugPreferenceConstants.CONSOLE_OPEN_ON_OUT));
        }
//        InputReadJob readJob = new InputReadJob(streamsProxy);
//        readJob.setSystem(true);
//        readJob.schedule();		
	}

    /**
     * Connects the given stream monitor to a new output stream with the given identifier.
     * 
     * @param streamMonitor stream monitor
     * @param streamIdentifier stream identifier
     * @param activateOnWrite whether the stream should displayed when written to 
     */
	@SuppressWarnings("resource")
	private IOConsoleOutputStream connect(IStreamMonitor streamMonitor, String streamIdentifier, boolean activateOnWrite) {
        IOConsoleOutputStream stream = null;
        if (fAllocateConsole) {

			stream = newOutputStream();
			Color color = fColorProvider.getColor(streamIdentifier);
			stream.setColor(color);
			stream.setActivateOnWrite(activateOnWrite);
        }
        synchronized (streamMonitor) {
            StreamListener listener = new StreamListener(streamIdentifier, streamMonitor, stream);
            fStreamListeners.add(listener);
        }
        
        return stream;
    }

	@Override
	public void connect(IStreamMonitor streamMonitor, String streamIdentifier) {
        connect(streamMonitor, streamIdentifier, false);
	}

	@Override
	public void addLink(IConsoleHyperlink link, int offset, int length) {
        try {
            addHyperlink(link, offset, length);
        } catch (BadLocationException e) {
            DebugUIPlugin.log(e);
        }
    }

	@Override
	public void addLink(IHyperlink link, int offset, int length) {
        try {
            addHyperlink(link, offset, length);
        } catch (BadLocationException e) {
            DebugUIPlugin.log(e);
        }		
	}

	@Override
	public IRegion getRegion(IConsoleHyperlink link) {
		return super.getRegion(link);
	}

	@Override
	public IProcess getProcess() {
		return null;
	}

	@Override
	public IOConsoleOutputStream getStream(String streamIdentifier) {
		return null;
	}

    /**
     * This class listens to a specified IO stream
     */
    private class StreamListener implements IStreamListener {

        private IOConsoleOutputStream fStream;

        private IStreamMonitor fStreamMonitor;

        private String fStreamId;

        private boolean fFlushed = false;

        private boolean fListenerRemoved = false;

        public StreamListener(String streamIdentifier, IStreamMonitor monitor, IOConsoleOutputStream stream) {
            this.fStreamId = streamIdentifier;
            this.fStreamMonitor = monitor;
            this.fStream = stream;
            fStreamMonitor.addListener(this);  
            //fix to bug 121454. Ensure that output to fast processes is processed.
            streamAppended(null, monitor);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.debug.core.IStreamListener#streamAppended(java.lang.String,
         *      org.eclipse.debug.core.model.IStreamMonitor)
         */
        @Override
		public void streamAppended(String text, IStreamMonitor monitor) {
            String encoding = getEncoding();
            if (fFlushed) {
                try {
                    if (fStream != null) {
                    	if (encoding == null) {
							fStream.write(text);
						} else {
							fStream.write(text.getBytes(encoding));
						}
                    }
//                    if (fFileOutputStream != null) {
//                        synchronized (fFileOutputStream) {
//                        	if (encoding == null) {
//								fFileOutputStream.write(text.getBytes());
//							} else {
//								fFileOutputStream.write(text.getBytes(encoding));
//							}
//                        }
//                    }
                } catch (IOException e) {
                    DebugUIPlugin.log(e);
                }
            } else {
                String contents = null;
                synchronized (fStreamMonitor) {
                    fFlushed = true;
                    contents = fStreamMonitor.getContents();
                    if (fStreamMonitor instanceof IFlushableStreamMonitor) {
                        IFlushableStreamMonitor m = (IFlushableStreamMonitor) fStreamMonitor;
                        m.flushContents();
                        m.setBuffered(false);
                    }
                }
                try {
                    if (contents != null && contents.length() > 0) {
                        if (fStream != null) {
                            fStream.write(contents);
                        }
//                        if (fFileOutputStream != null) {
//                            synchronized (fFileOutputStream) {
//                                fFileOutputStream.write(contents.getBytes());
//                            }
//                        }
                    }
                } catch (IOException e) {
                    DebugUIPlugin.log(e);
                }
            }
        }

        public void closeStream() {
            if (fStreamMonitor == null) {
                return;
            }
            synchronized (fStreamMonitor) {
                fStreamMonitor.removeListener(this);
                if (!fFlushed) {
                    String contents = fStreamMonitor.getContents();
                    streamAppended(contents, fStreamMonitor);
                }
                fListenerRemoved = true;
                try {
                    if (fStream != null) {
                        fStream.close();
                    }
                } catch (IOException e) {
                }
            }
        }

        public void dispose() {
            if (!fListenerRemoved) {
                closeStream();
            }
            fStream = null;
            fStreamMonitor = null;
            fStreamId = null;
        }
    }
    
//    private class InputReadJob extends Job {
//
//        private IStreamsProxy streamsProxy;
//
//        InputReadJob(IStreamsProxy streamsProxy) {
//            super("SVEBuildConsole Input Job"); //$NON-NLS-1$
//            this.streamsProxy = streamsProxy;
//        }
//
//        /*
//         * (non-Javadoc)
//         * 
//         * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
//         */
//        @Override
//		protected IStatus run(IProgressMonitor monitor) {
//            String encoding = getEncoding();
//            try {
//                byte[] b = new byte[1024];
//                int read = 0;
//                while (fInput != null && read >= 0) {
//                    read = fInput.read(b);
//                    if (read > 0) {
//                        String s;
//                        if (encoding != null) {
//							s = new String(b, 0, read, encoding);
//						} else {
//							s = new String(b, 0, read);
//						}
//                        streamsProxy.write(s);
//                    }
//                }
//            } catch (IOException e) {
//                DebugUIPlugin.log(e);
//            }
//            return Status.OK_STATUS;
//        }
//    }

}
