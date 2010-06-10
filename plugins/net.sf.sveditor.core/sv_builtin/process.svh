

__sv_builtin class process;

	enum state { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED };
	
	static extern function process self();
	
	extern function state status();
	
	extern function void kill();
	
	extern task await();
	
	extern function void suspend();
	
	extern task resume();
	
endclass
