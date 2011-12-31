
class c;
	
	typedef struct packed { // default unsigned
		bit [3:0] GFC;
		bit [7:0] VPI;
		bit [11:0] VCI;
		bit CLP;
		bit [3:0] PT ;
		bit [7:0] HEC;
		bit [47:0] [7:0] Payload;
		bit [2:0] filler;
	} s_atmcell;	
	
endclass