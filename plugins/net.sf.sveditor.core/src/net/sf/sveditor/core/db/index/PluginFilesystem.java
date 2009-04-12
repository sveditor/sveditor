package net.sf.sveditor.core.db.index;

import java.net.URI;

import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileSystem;

public class PluginFilesystem extends FileSystem {

	public PluginFilesystem() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public IFileStore getStore(URI uri) {
		return new PluginFileStore(uri);
	}
}
