

class __sv_builtin_covergroup_options;
//	int 	weight;
	
	real 	goal;
	
	string 	name;
	
	string 	comment;
	
	int		at_least;
	
	bit		detect_overlap;
	
	int		auto_bin_max;
	
	bit		per_instance;
	
	bit		cross_num_print_missing;
	
endclass

class __sv_builtin_covergroup;

	extern function new();
	
	__sv_builtin_covergroup_options options;

	extern function real get_coverage();
	
	extern function void sample();
	
	extern function real get_inst_coverage();
	
	extern function void set_inst_name(string);

	extern function void start();

	extern function void stop();

endclass

class __sv_builtin_coverpoint_options;
	int 	weight;
	
	real 	goal;
	
	string 	comment;
	
	int		at_least;
	
	bit		detect_overlap;
	
	int		auto_bin_max;
	
endclass


class __sv_builtin_coverpoint;

	__sv_builtin_coverpoint_options		options;

	extern function real get_coverage();
	
	extern function real get_inst_coverage();
	
	extern function void start();

	extern function void stop();

endclass

class __sv_builtin_coverpoint_cross_options;
	int 	weight;
	
	real 	goal;
	
	string 	comment;
	
	int		at_least;
	
endclass

class __sv_builtin_coverpoint_cross;

	__sv_builtin_coverpoint_cross_options		options;

	extern function real get_coverage();
	
	extern function real get_inst_coverage();
	
	extern function void start();

	extern function void stop();

endclass
