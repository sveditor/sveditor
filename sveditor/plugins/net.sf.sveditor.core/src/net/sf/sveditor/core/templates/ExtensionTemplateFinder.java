package net.sf.sveditor.core.templates;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class ExtensionTemplateFinder extends AbstractTemplateFinder {
	
	public ExtensionTemplateFinder() {
		super();
		fLog = LogFactory.getLogHandle("ExtensionTemplateFinder");
	}

	public void find() {
		IExtensionRegistry ext_rgy = Platform.getExtensionRegistry();
		IExtensionPoint ext_pt = ext_rgy.getExtensionPoint(
				SVCorePlugin.PLUGIN_ID, "SVTemplates");
		IExtension ext_list[] = ext_pt.getExtensions();
		
		for (IExtension ext : ext_list) {
			IConfigurationElement ce_l[] = ext.getConfigurationElements();

			for (IConfigurationElement ce : ce_l) {
				String name = ce.getName();
				if (name.equals("category")) {
					addCategory(ce);
				} else if (name.equals("template")) {
					addTemplate(ce);
				} else {
					fLog.error("Unknown SVTemplate element \"" + 
							name + "\"");
				}
			}
		}
	}
	
	private void addCategory(IConfigurationElement ce) {
		String id		= ce.getAttribute("id");
		String name 	= ce.getAttribute("name");
		String parent   = ce.getAttribute("parent");
		TemplateCategory c = new TemplateCategory(id, name, parent);
		
		for (IConfigurationElement ci : ce.getChildren()) {
			if (ci.getName().equals("description")) {
				c.setDescription(ci.getValue());
			}
		}
		
		fCategories.add(c);
	}
	
	private void addTemplate(IConfigurationElement ce) {
		String id				= ce.getAttribute("id");
		String name				= ce.getAttribute("name");
		String category			= ce.getAttribute("category");
		String description		= "";
		Bundle bundle 			= Platform.getBundle(ce.getContributor().getName());
		
		for (IConfigurationElement ce_c : ce.getChildren()) {
			if (ce_c.getName().equals("description")) {
				description = ce_c.getValue();
			}
		}

		TemplateInfo info = new TemplateInfo(id, name, category, description, 
				new PluginInStreamProvider(bundle));
		fTemplates.add(info);
		
		for (IConfigurationElement ce_c : ce.getChildren()) {
			if (ce_c.getName().equals("files")) {
				for (IConfigurationElement tmpl : ce_c.getChildren()) {
					String template = tmpl.getAttribute("template");
					String tmpl_name = tmpl.getAttribute("name");
					String executable = tmpl.getAttribute("execute");
					info.addTemplate(new Tuple<String, String>(template, tmpl_name));
					info.setExecutable(template, 
							(executable != null && executable.equals("true")));
				}
			} else if (ce_c.getName().equals("parameters")) {
				for (IConfigurationElement p : ce_c.getChildren()) {
					if (p.getName().equals("parameter")) {
						String p_type = p.getAttribute("type");
						String p_name = p.getAttribute("name");
						String p_dflt = p.getAttribute("default");
						String p_ext_from = p.getAttribute("extends_from");
						String p_restr = p.getAttribute("restrictions");
						
						TemplateParameterType type = null;
						
						if (p_type.equals("int")) {
							type = TemplateParameterType.ParameterType_Int;
						} else if (p_type.equals("id")) {
							type = TemplateParameterType.ParameterType_Id;
						} else if (p_type.equals("class")) {
							type = TemplateParameterType.ParameterType_Class;
						} else {
							fLog.error("Unknown parameter type \"" + p_type + "\"");
							continue;
						}
						
						TemplateParameter tp = new TemplateParameter(
								type, p_name, p_dflt, p_ext_from);
						
						if (p_restr != null && !p_restr.trim().equals("")) {
							String r[] = p_restr.split(",");
							for (String rs : r) {
								rs = rs.trim();
								if (!rs.equals("")) {
									tp.addValue(rs);
								}
							}
						}
						
						info.addParameter(tp);
					}
				}
			}
		} 
	}
}
