package net.sf.sveditor.core.db.index;

public class SVDBPluginLibDescriptor {
	
	private String					fName;
	private String					fId;
	private String					fNamespace;
	private String					fPath;
	private boolean					fIsDefault;
	private String					fDescription;
	
	public SVDBPluginLibDescriptor(
			String				name,
			String				id,
			String				namespace,
			String				path,
			boolean				is_default,
			String				description) {
		fName        = name;
		fId          = id;
		fNamespace   = namespace;
		fPath        = path;
		fIsDefault   = is_default;
		fDescription = description;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getId() {
		return fId;
	}
	
	public String getPath() {
		return fPath;
	}

	public String getNamespace() {
		return fNamespace;
	}

	public boolean isDefault() {
		return fIsDefault;
	}
	
	public String getDescription() {
		return fDescription;
	}
}
