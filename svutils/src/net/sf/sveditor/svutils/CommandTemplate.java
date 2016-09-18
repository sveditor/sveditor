package net.sf.sveditor.svutils;

import java.util.List;

import net.sf.sveditor.svt.core.templates.FilesystemTemplateRegistry;

public class CommandTemplate extends CommandBase {
	private FilesystemTemplateRegistry			fTemplateRgy;
	
	public CommandTemplate() {
		super("template");
	}
	
	protected void print_help() {
		System.out.println("svutils template [subcommand] [options] [arguments]");
	}
	
	@Override
	public int run(List<Argument> args) {
		
		// First, check whether we have a '-help' switch
		boolean help_requested = false;
		for (int i=1; i<args.size(); i++) {
			Argument a = args.get(i);
			
			if (a.fArg.startsWith("-")) {
				if (a.fArg.equals("-help")) {
					help_requested = true;
					break;
				}
			} else {
				break;
			}
		}
		
		if (help_requested || args.size() == 1) {
			print_help();
			return 0;
		}
		
		return 0;
	}

}
