//////////////////////////////////////////////////////////////////////
////                                                              ////
////  eth_miim.v                                                  ////
////                                                              ////
////  This file is part of the Ethernet IP core project           ////
////  http://www.opencores.org/projects/ethmac/                   ////
////                                                              ////
////  Author(s):                                                  ////
////      - Igor Mohor (igorM@opencores.org)                      ////
////                                                              ////
////  All additional information is avaliable in the Readme.txt   ////
////  file.                                                       ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2001 Authors                                   ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// CVS Revision History
//
// $Log: eth_miim.v,v $
// Revision 1.1  2005/10/18 20:26:40  janick
// *** empty log message ***
//
// Revision 1.1  2004/10/01 18:02:57  janick
// Initial version, obtained from OpenCores.org on 04/10/01
//
// Revision 1.5  2003/05/16 10:08:27  mohor
// Busy was set 2 cycles too late. Reported by Dennis Scott.
//
// Revision 1.4  2002/08/14 18:32:10  mohor
// - Busy signal was not set on time when scan status operation was performed
// and clock was divided with more than 2.
// - Nvalid remains valid two more clocks (was previously cleared too soon).
//
// Revision 1.3  2002/01/23 10:28:16  mohor
// Link in the header changed.
//
// Revision 1.2  2001/10/19 08:43:51  mohor
// eth_timescale.v changed to timescale.v This is done because of the
// simulation of the few cores in a one joined project.
//
// Revision 1.1  2001/08/06 14:44:29  mohor
// A define FPGA added to select between Artisan RAM (for ASIC) and Block Ram (For Virtex).
// Include files fixed to contain no path.
// File names and module names changed ta have a eth_ prologue in the name.
// File eth_timescale.v is used to define timescale
// All pin names on the top module are changed to contain _I, _O or _OE at the end.
// Bidirectional signal MDIO is changed to three signals (Mdc_O, Mdi_I, Mdo_O
// and Mdo_OE. The bidirectional signal must be created on the top level. This
// is done due to the ASIC tools.
//
// Revision 1.2  2001/08/02 09:25:31  mohor
// Unconnected signals are now connected.
//
// Revision 1.1  2001/07/30 21:23:42  mohor
// Directory structure changed. Files checked and joind together.
//
// Revision 1.3  2001/06/01 22:28:56  mohor
// This files (MIIM) are fully working. They were thoroughly tested. The testbench is not updated.
//
//

`include "timescale.v"


module eth_miim
(
  Clk,
  Reset,
  Divider,
  NoPre,
  CtrlData,
  Rgad,
  Fiad,
  WCtrlData,
  RStat,
  ScanStat,
  Mdi,
  Mdo,
  MdoEn,
  Mdc,
  Busy,
  Prsd,
  LinkFail,
  Nvalid,
  WCtrlDataStart,
  RStatStart,
  UpdateMIIRX_DATAReg
);



input         Clk;                // Host Clock
input         Reset;              // General Reset
input   [7:0] Divider;            // Divider for the host clock
input  [15:0] CtrlData;           // Control Data (to be written to the PHY reg.)
input   [4:0] Rgad;               // Register Address (within the PHY)
input   [4:0] Fiad;               // PHY Address
input         NoPre;              // No Preamble (no 32-bit preamble)
input         WCtrlData;          // Write Control Data operation
input         RStat;              // Read Status operation
input         ScanStat;           // Scan Status operation
input         Mdi;                // MII Management Data In

output        Mdc;                // MII Management Data Clock
output        Mdo;                // MII Management Data Output
output        MdoEn;              // MII Management Data Output Enable
output        Busy;               // Busy Signal
output        LinkFail;           // Link Integrity Signal
output        Nvalid;             // Invalid Status (qualifier for the valid scan result)

output [15:0] Prsd;               // Read Status Data (data read from the PHY)

output        WCtrlDataStart;     // This signals resets the WCTRLDATA bit in the MIIM Command register
output        RStatStart;         // This signal resets the RSTAT BIT in the MIIM Command register
output        UpdateMIIRX_DATAReg;// Updates MII RX_DATA register with read data

parameter Tp = 1;


reg           Nvalid;
reg           EndBusy_d;          // Pre-end Busy signal
reg           EndBusy;            // End Busy signal (stops the operation in progress)

reg           WCtrlData_q1;       // Write Control Data operation delayed 1 Clk cycle
reg           WCtrlData_q2;       // Write Control Data operation delayed 2 Clk cycles
reg           WCtrlData_q3;       // Write Control Data operation delayed 3 Clk cycles
reg           WCtrlDataStart;     // Start Write Control Data Command (positive edge detected)
reg           WCtrlDataStart_q;
reg           WCtrlDataStart_q1;  // Start Write Control Data Command delayed 1 Mdc cycle
reg           WCtrlDataStart_q2;  // Start Write Control Data Command delayed 2 Mdc cycles

reg           RStat_q1;           // Read Status operation delayed 1 Clk cycle
reg           RStat_q2;           // Read Status operation delayed 2 Clk cycles
reg           RStat_q3;           // Read Status operation delayed 3 Clk cycles
reg           RStatStart;         // Start Read Status Command (positive edge detected)
reg           RStatStart_q1;      // Start Read Status Command delayed 1 Mdc cycle
reg           RStatStart_q2;      // Start Read Status Command delayed 2 Mdc cycles

reg           ScanStat_q1;        // Scan Status operation delayed 1 cycle
reg           ScanStat_q2;        // Scan Status operation delayed 2 cycles
reg           SyncStatMdcEn;      // Scan Status operation delayed at least cycles and synchronized to MdcEn

wire          WriteDataOp;        // Write Data Operation (positive edge detected)
wire          ReadStatusOp;       // Read Status Operation (positive edge detected)
wire          ScanStatusOp;       // Scan Status Operation (positive edge detected)
wire          StartOp;            // Start Operation (start of any of the preceding operations)
wire          EndOp;              // End of Operation

reg           InProgress;         // Operation in progress
reg           InProgress_q1;      // Operation in progress delayed 1 Mdc cycle
reg           InProgress_q2;      // Operation in progress delayed 2 Mdc cycles
reg           InProgress_q3;      // Operation in progress delayed 3 Mdc cycles

reg           WriteOp;            // Write Operation Latch (When asserted, write operation is in progress)
reg     [6:0] BitCounter;         // Bit Counter


wire          MdcFrame;           // Frame window for limiting the Mdc
wire    [3:0] ByteSelect;         // Byte Select defines which byte (preamble, data, operation, etc.) is loaded and shifted through the shift register.
wire          MdcEn;              // MII Management Data Clock Enable signal is asserted for one Clk period before Mdc rises.
wire          ShiftedBit;         // This bit is output of the shift register and is connected to the Mdo signal


wire          LatchByte1_d2;
wire          LatchByte0_d2;
reg           LatchByte1_d;
reg           LatchByte0_d;
reg     [1:0] LatchByte;          // Latch Byte selects which part of Read Status Data is updated from the shift register

reg           UpdateMIIRX_DATAReg;// Updates MII RX_DATA register with read data





// Generation of the EndBusy signal. It is used for ending the MII Management operation.
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    begin
      EndBusy_d <= #Tp 1'b0;
      EndBusy <= #Tp 1'b0;
    end
  else
    begin
      EndBusy_d <= #Tp ~InProgress_q2 & InProgress_q3;
      EndBusy   <= #Tp EndBusy_d;
    end
end


// Update MII RX_DATA register
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    UpdateMIIRX_DATAReg <= #Tp 0;
  else
  if(EndBusy & ~WCtrlDataStart_q)
    UpdateMIIRX_DATAReg <= #Tp 1;
  else
    UpdateMIIRX_DATAReg <= #Tp 0;    
end



// Generation of the delayed signals used for positive edge triggering.
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    begin
      WCtrlData_q1 <= #Tp 1'b0;
      WCtrlData_q2 <= #Tp 1'b0;
      WCtrlData_q3 <= #Tp 1'b0;
      
      RStat_q1 <= #Tp 1'b0;
      RStat_q2 <= #Tp 1'b0;
      RStat_q3 <= #Tp 1'b0;

      ScanStat_q1  <= #Tp 1'b0;
      ScanStat_q2  <= #Tp 1'b0;
      SyncStatMdcEn <= #Tp 1'b0;
    end
  else
    begin
      WCtrlData_q1 <= #Tp WCtrlData;
      WCtrlData_q2 <= #Tp WCtrlData_q1;
      WCtrlData_q3 <= #Tp WCtrlData_q2;

      RStat_q1 <= #Tp RStat;
      RStat_q2 <= #Tp RStat_q1;
      RStat_q3 <= #Tp RStat_q2;

      ScanStat_q1  <= #Tp ScanStat;
      ScanStat_q2  <= #Tp ScanStat_q1;
      if(MdcEn)
        SyncStatMdcEn  <= #Tp ScanStat_q2;
    end
end


// Generation of the Start Commands (Write Control Data or Read Status)
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    begin
      WCtrlDataStart <= #Tp 1'b0;
      WCtrlDataStart_q <= #Tp 1'b0;
      RStatStart <= #Tp 1'b0;
    end
  else
    begin
      if(EndBusy)
        begin
          WCtrlDataStart <= #Tp 1'b0;
          RStatStart <= #Tp 1'b0;
        end
      else
        begin
          if(WCtrlData_q2 & ~WCtrlData_q3)
            WCtrlDataStart <= #Tp 1'b1;
          if(RStat_q2 & ~RStat_q3)
            RStatStart <= #Tp 1'b1;
          WCtrlDataStart_q <= #Tp WCtrlDataStart;
        end
    end
end 


// Generation of the Nvalid signal (indicates when the status is invalid)
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    Nvalid <= #Tp 1'b0;
  else
    begin
      if(~InProgress_q2 & InProgress_q3)
        begin
          Nvalid <= #Tp 1'b0;
        end
      else
        begin
          if(ScanStat_q2  & ~SyncStatMdcEn)
            Nvalid <= #Tp 1'b1;
        end
    end
end 

// Signals used for the generation of the Operation signals (positive edge)
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    begin
      WCtrlDataStart_q1 <= #Tp 1'b0;
      WCtrlDataStart_q2 <= #Tp 1'b0;

      RStatStart_q1 <= #Tp 1'b0;
      RStatStart_q2 <= #Tp 1'b0;

      InProgress_q1 <= #Tp 1'b0;
      InProgress_q2 <= #Tp 1'b0;
      InProgress_q3 <= #Tp 1'b0;

  	  LatchByte0_d <= #Tp 1'b0;
  	  LatchByte1_d <= #Tp 1'b0;

  	  LatchByte <= #Tp 2'b00;
    end
  else
    begin
      if(MdcEn)
        begin
          WCtrlDataStart_q1 <= #Tp WCtrlDataStart;
          WCtrlDataStart_q2 <= #Tp WCtrlDataStart_q1;

          RStatStart_q1 <= #Tp RStatStart;
          RStatStart_q2 <= #Tp RStatStart_q1;

          LatchByte[0] <= #Tp LatchByte0_d;
          LatchByte[1] <= #Tp LatchByte1_d;

          LatchByte0_d <= #Tp LatchByte0_d2;
          LatchByte1_d <= #Tp LatchByte1_d2;

          InProgress_q1 <= #Tp InProgress;
          InProgress_q2 <= #Tp InProgress_q1;
          InProgress_q3 <= #Tp InProgress_q2;
        end
    end
end 


// Generation of the Operation signals
assign WriteDataOp  = WCtrlDataStart_q1 & ~WCtrlDataStart_q2;    
assign ReadStatusOp = RStatStart_q1     & ~RStatStart_q2;
assign ScanStatusOp = SyncStatMdcEn     & ~InProgress & ~InProgress_q1 & ~InProgress_q2;
assign StartOp      = WriteDataOp | ReadStatusOp | ScanStatusOp;

// Busy
assign Busy = WCtrlData | WCtrlDataStart | RStat | RStatStart | SyncStatMdcEn | EndBusy | InProgress | InProgress_q3 | Nvalid;


// Generation of the InProgress signal (indicates when an operation is in progress)
// Generation of the WriteOp signal (indicates when a write is in progress)
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    begin
      InProgress <= #Tp 1'b0;
      WriteOp <= #Tp 1'b0;
    end
  else
    begin
      if(MdcEn)
        begin
          if(StartOp)
            begin
              if(~InProgress)
                WriteOp <= #Tp WriteDataOp;
              InProgress <= #Tp 1'b1;
            end
          else
            begin
              if(EndOp)
                begin
                  InProgress <= #Tp 1'b0;
                  WriteOp <= #Tp 1'b0;
                end
            end
        end
    end
end



// Bit Counter counts from 0 to 63 (from 32 to 63 when NoPre is asserted)
always @ (posedge Clk or posedge Reset)
begin
  if(Reset)
    BitCounter[6:0] <= #Tp 7'h0;
  else
    begin
      if(MdcEn)
        begin
          if(InProgress)
            begin
              if(NoPre & ( BitCounter == 7'h0 ))
                BitCounter[6:0] <= #Tp 7'h21;
              else
                BitCounter[6:0] <= #Tp BitCounter[6:0] + 1'b1;
            end
          else
            BitCounter[6:0] <= #Tp 7'h0;
        end
    end
end


// Operation ends when the Bit Counter reaches 63
assign EndOp = BitCounter==63;

assign ByteSelect[0] = InProgress & ((NoPre & (BitCounter == 7'h0)) | (~NoPre & (BitCounter == 7'h20)));
assign ByteSelect[1] = InProgress & (BitCounter == 7'h28);
assign ByteSelect[2] = InProgress & WriteOp & (BitCounter == 7'h30);
assign ByteSelect[3] = InProgress & WriteOp & (BitCounter == 7'h38);


// Latch Byte selects which part of Read Status Data is updated from the shift register
assign LatchByte1_d2 = InProgress & ~WriteOp & BitCounter == 7'h37;
assign LatchByte0_d2 = InProgress & ~WriteOp & BitCounter == 7'h3F;


// Connecting the Clock Generator Module
eth_clockgen clkgen(.Clk(Clk), .Reset(Reset), .Divider(Divider[7:0]), .MdcEn(MdcEn), .MdcEn_n(MdcEn_n), .Mdc(Mdc) 
                   );

// Connecting the Shift Register Module
eth_shiftreg shftrg(.Clk(Clk), .Reset(Reset), .MdcEn_n(MdcEn_n), .Mdi(Mdi), .Fiad(Fiad), .Rgad(Rgad), 
                    .CtrlData(CtrlData), .WriteOp(WriteOp), .ByteSelect(ByteSelect), .LatchByte(LatchByte), 
                    .ShiftedBit(ShiftedBit), .Prsd(Prsd), .LinkFail(LinkFail)
                   );

// Connecting the Output Control Module
eth_outputcontrol outctrl(.Clk(Clk), .Reset(Reset), .MdcEn_n(MdcEn_n), .InProgress(InProgress), 
                          .ShiftedBit(ShiftedBit), .BitCounter(BitCounter), .WriteOp(WriteOp), .NoPre(NoPre), 
                          .Mdo(Mdo), .MdoEn(MdoEn)
                         );

endmodule
