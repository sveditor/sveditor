
`define vmm_channel_(T) T``_channel

`define vmm_channel(T) \
class `vmm_channel_(T) extends vmm_channel; \
 \
   function new(string name, \
                string inst, \
                int    full = 1, \
                int    empty = 0, \
                bit    fill_as_bytes = 0); \
      super.new(name, inst, full, empty, fill_as_bytes); \
   endfunction: new \
 \
   function T unput(int offset = -1); \
      $cast(unput, super.unput(offset)); \
   endfunction: unput \
 \
   task get(output T obj, input int offset = 0); \
      vmm_data o; \
      super.get(o, offset); \
      $cast(obj, o); \
   endtask: get \
 \
   task peek(output T obj, input int offset = 0); \
      vmm_data o; \
      super.peek(o, offset); \
      $cast(obj, o); \
   endtask: peek \
 \
   function T try_peek(int offset = 0); \
      vmm_data o; \
      o = super.try_peek(offset); \
      $cast(try_peek, o); \
   endfunction: try_peek \
 \
   task activate(output T obj, input int offset = 0); \
      vmm_data o; \
      super.activate(o, offset); \
      $cast(obj, o); \
   endtask: activate \
 \
   function T active_slot(); \
      $cast(active_slot, super.active_slot()); \
   endfunction: active_slot \
 \
   function T start(); \
      $cast(start, super.start()); \
   endfunction: start \
 \
   function T complete(vmm_data status = null); \
      $cast(complete, super.complete(status)); \
   endfunction: complete \
 \
   function T remove(); \
      $cast(remove, super.remove()); \
   endfunction: remove \
 \
   task tee(output T obj); \
      vmm_data o; \
      super.tee(o); \
      $cast(obj, o); \
   endtask: tee \
 \
   function T for_each(bit reset = 0); \
      $cast(for_each, super.for_each(reset)); \
   endfunction: for_each \
 \
endclass
