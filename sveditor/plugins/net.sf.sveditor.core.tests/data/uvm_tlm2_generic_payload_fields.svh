
`include "uvm_macros.svh"

class uvm_tlm2_generic_payload_fields;
  function void do_record(uvm_recorder recorder);
    if (!is_recording_enabled())
      return;
    super.do_record(recorder);
    `uvm_record_field("address",m_address)
    `uvm_record_field("command",m_command.name())
    `uvm_record_field("data_length",m_length)
    `uvm_record_field("byte_enable_length",m_length)
    `uvm_record_field("response_status",m_response_status.name())
    `uvm_record_field("streaming_width",m_streaming_width)

    for (int i=0; i < m_length; i++)
      `uvm_record_field($sformatf("\\data[%0d] ", i), m_data[i])

    for (int i=0; i < m_byte_enable_length; i++)
      `uvm_record_field($sformatf("\\byte_en[%0d] ", i), m_byte_enable[i])

    foreach (m_extensions[ext])
      m_extensions[ext].record(recorder);
  endfunction
endclass
