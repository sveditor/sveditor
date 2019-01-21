package net.sf.sveditor.core;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.content.IContentTypeManager;
import org.eclipse.core.runtime.content.IContentTypeManager.ContentTypeChangeEvent;
import org.eclipse.core.runtime.content.IContentTypeManager.IContentTypeChangeListener;

public class ContentTypeFileExtProvider implements IFileExtProvider {
	private Set<String>				fSVRootFileExts;
	private Set<String>				fVLRootFileExts;
	private Set<String>				fSVFileExts;
	private Set<String>				fVLFileExts;
	
	public ContentTypeFileExtProvider() {
		IContentTypeManager mgr = Platform.getContentTypeManager();
		mgr.addContentTypeChangeListener(fContentTypeListener);
		// TODO Auto-generated constructor stub
	}
	
	public void dispose() {
		IContentTypeManager mgr = Platform.getContentTypeManager();

		mgr.removeContentTypeChangeListener(fContentTypeListener);
	}
	
	private IContentTypeChangeListener fContentTypeListener = new IContentTypeChangeListener() {
		
		@Override
		public void contentTypeChanged(ContentTypeChangeEvent event) {
			fSVFileExts = null;
			fVLFileExts = null;
			fSVRootFileExts = null;
			fVLRootFileExts = null;
		}
	};
	

	@Override
	public Set<String> getSVRootFileExts() {
		if (fSVRootFileExts == null) {
			fSVRootFileExts = new HashSet<String>();

			IContentTypeManager mgr = Platform.getContentTypeManager();
			
			for (String type_s : new String[] {
					SVCorePlugin.PLUGIN_ID + ".systemverilog-rootfiles"}) {
				IContentType type = mgr.getContentType(type_s);
				String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

				for (String e : exts) {
					fSVRootFileExts.add(e);
				}
			}
		}
		
		return fSVRootFileExts;
	}

	@Override
	public Set<String> getSVFileExts() {
		if (fSVFileExts == null) {
			fSVFileExts = new HashSet<String>();

			IContentTypeManager mgr = Platform.getContentTypeManager();
			
			for (String type_s : new String[] {
					SVCorePlugin.PLUGIN_ID + ".systemverilog"}) {
				IContentType type = mgr.getContentType(type_s);
				String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

				for (String e : exts) {
					fSVFileExts.add(e);
				}
			}
		}
		
		return fSVFileExts;
	}

	@Override
	public Set<String> getVLRootFileExts() {
		if (fVLRootFileExts == null) {
			fVLRootFileExts = new HashSet<String>();

			IContentTypeManager mgr = Platform.getContentTypeManager();
			
			for (String type_s : new String[] {
					SVCorePlugin.PLUGIN_ID + ".verilog-rootfiles"}) {
				IContentType type = mgr.getContentType(type_s);
				String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

				for (String e : exts) {
					fVLRootFileExts.add(e);
				}
			}
		}
		
		return fVLRootFileExts;		
	}

	@Override
	public Set<String> getVLFileExts() {
		if (fVLFileExts == null) {
			fVLFileExts = new HashSet<String>();

			IContentTypeManager mgr = Platform.getContentTypeManager();
			
			for (String type_s : new String[] {
					SVCorePlugin.PLUGIN_ID + ".verilog"}) {
				IContentType type = mgr.getContentType(type_s);
				String exts[] = type.getFileSpecs(IContentType.FILE_EXTENSION_SPEC);

				for (String e : exts) {
					fVLFileExts.add(e);
				}
			}
		}
		
		return fVLFileExts;		
	}

}
