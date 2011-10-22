
class c;
	
task read(int j = 0, int k, int data = 1 );
	// empty
endtask

task do_something();
	read( , 5 ); // is equivalent to read( 0, 5, 1 );
	read( 2, 5 ); // is equivalent to read( 2, 5, 1 );
	read( , 5, ); // is equivalent to read( 0, 5, 1 );
	read( , 5, 7 ); // is equivalent to read( 0, 5, 7 );
	read( 1, 5, 2 ); // is equivalent to read( 1, 5, 2 );
endtask

endclass