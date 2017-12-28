
__sv_builtin class semaphore;

	extern function new(int keyCount = 0);
	
	extern function void put(int keyCount = 1);
	
	extern task get(int keyCount = 1);
	
	extern function int try_get(int keyCount = 1);
endclass
