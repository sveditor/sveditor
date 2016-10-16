package net.sf.sveditor.svutils;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogListener;
import net.sf.sveditor.core.log.LogFactory;

public class SVUtils implements ILogListener {
	
	private String			commands[] = {
			"template", "          - Generate sources using SV Templates"
	};
	private CommandBase		command_h[] = {
			new CommandTemplate()
	};
	
	private boolean			fHookLog = true;
	
	public SVUtils() {
		
	}
	
	@Override
	public void message(ILogHandle handle, int type, int level, String message) {
		switch (type) {
		case ILogListener.Type_Info:
			System.out.println(message);
			break;
			
		case ILogListener.Type_Error:
			System.out.println("[ERROR: " + handle.getName() + "] " + message);
			break;
			
		case ILogListener.Type_Debug:
			break;
		}
	}

	public int run(String args[]) {
		List<Argument> all_args = new ArrayList<Argument>();
		
		if (fHookLog) {
			LogFactory.getDefault().addLogListener(this);
		}
		
		// First, expand out any argument files
		// TODO: for now, just copy arguments over
		for (String arg : args) {
			all_args.add(new Argument(arg));
		}
		
		// Next, see if help was requested
		boolean help_requested = false;
		for (int i=0; i<all_args.size(); i++) {
			Argument arg = all_args.get(i);
			
			if (arg.fArg.startsWith("-")) {
				if (arg.fArg.equals("-help")) {
					help_requested = true;
					break;
				}
			} else {
				break;
			}
		}
		
		if (help_requested || all_args.size() == 0) {
			print_help();
			LogFactory.getDefault().removeLogListener(this);
			return 0;
		}
	
		// Process arguments
		int idx=0;
		int ret=1;
	
		String cmd = all_args.get(0).fArg;
		
		for (int i=0; i<command_h.length; i++) {
			if (commands[2*i].equals(cmd)) {
				ret = command_h[i].run(all_args);
				break;
			}
		}
		
		
		LogFactory.getDefault().removeLogListener(this);
		
		return ret;
	}
	
	private void print_help() {
		System.out.println("svutils [options] [subcommand] [options]");
		System.out.println("  Global options:");
		System.out.println("    -help      - display this message");
		System.out.println("    -f <file>  - read arguments from <file>");
		System.out.println("    -F <file>  - read arguments from <file>");
		System.out.println();
		System.out.println("  Subcommands:");
		for (String cmd : commands) {
			System.out.println("    " + cmd);
		}
	}

	public static void main(String[] args) {
		SVUtils svu = new SVUtils();
		
		System.exit(svu.run(args));
	}

}
