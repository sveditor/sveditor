
__sv_builtin class mailbox #(type T = dynamic_singular_type) ;
  extern function new(int bound = 0);
  
  extern function int num();
  
  extern task put( T message);
  
  extern function int try_put( T message);
  
  extern task get( ref T message );
  
  extern function int try_get( ref T message );
  
  extern task peek( ref T message );
  
  extern function int try_peek( ref T message );
  
endclass
