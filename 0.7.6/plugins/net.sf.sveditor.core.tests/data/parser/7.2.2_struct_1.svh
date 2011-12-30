class c;
	
	typedef struct {
		int addr = 1 + constant;
		int crc;
		byte data [4] = '{4{1}};
	} packet1;

	packet1 p1;
	
	packet1 pi = '{1,2,'{2,3,4,5}};
	
endclass
