/****************************************************************************
 * string.svh
 *
 * Definition of built-in class 'string'
 ****************************************************************************/
 
class string;


	/****************************************************************
	 * len()
	 *
	 * Returns the length of this string
	 ****************************************************************/
	extern function int len();

	/****************************************************************
	 * putc()
	 *
	 * Inserts a character in this string
	 ****************************************************************/
    extern task putc(int i, byte c);

	/****************************************************************
	 * getc()
	 *
	 * Returns the character at the specified index 
	 ****************************************************************/
    extern function byte getc(int i);
    
	/****************************************************************
	 * toupper()
	 *
	 * Returns a copy of this string with all characters converted
	 * to upper-case 
	 ****************************************************************/
    extern function string toupper();
    
	/****************************************************************
	 * tolower()
	 *
	 * Returns a copy of this string with all characters converted
	 * to lower-case 
	 ****************************************************************/
    extern function string tolower();
    
	/****************************************************************
	 * compare()
	 *
	 * Compare string 's' to this string
	 ****************************************************************/
    extern function int compare(string s);
    
	/****************************************************************
	 * icompare()
	 
	 * Compare string 's' to this string in a case-insensitive manner
	 ****************************************************************/
	extern function int icompare(string s);
	
	    
	/****************************************************************
	 * substr()
	 *
	 * Returns a sub-string of this string, ranging from index i to j
	 ****************************************************************/
	extern function string substr(int i, int j);
	
	/****************************************************************
	 ****************************************************************/
	extern function integer atoi();
	
	extern function integer atohex();
	
	extern function integer atooct();
	
	extern function integer atobin();
	
	extern function real atoreal();
	
	extern task itoa(integer i);
	
	extern task hextoa(integer i);
	
	extern task octtoa(integer i);
	
	extern task bintoa(integer i);
	
	extern task realtoa(real r);
	
endclass

