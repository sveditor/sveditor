package net.sf.sveditor.core.methodology_templates;

public class MethodologyTemplate {
	private String				fId;
	private String				fName;
	private String				fCategoryId;
	private String				fTemplate;
	
	public MethodologyTemplate(String id, String name, String category_id) {
		fId = id;
		fName = name;
		fCategoryId = (category_id != null)?category_id:"";
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getCategoryId() {
		return fCategoryId;
	}
	
	public String getTemplate() {
		return fTemplate;
	}
	
	public void setTemplate(String template) {
		fTemplate = template;
	}

}
