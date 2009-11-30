

class __sv_queue #(type T=int);

	extern function int size();
	
	extern function void insert(int index, T elem);
	
	extern function void delete(int index);
	
	extern function T pop_front();
	
	extern function T pop_back();
	
	extern function void push_front(T elem);
	
	extern function void push_back(T elem);

endclass
