

__sv_builtin class process;

	typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;
	
	static extern function process self();
	
	extern function state status();
	
	extern function void kill();
	
	extern task await();
	
	extern function void suspend();
	
	extern task resume();
	
endclass
