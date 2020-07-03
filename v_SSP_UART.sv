// This module contains assertions for top level SSP_UART 
// This assumes that instantiated modules have been verified using previous assertions files
// i.e. The empty flag of the recieve FIFO or TXSM state machine function correctly 

module ssp_uart_props #(
    parameter pPS_Default   = 4'h1,        
    parameter pDiv_Default  = 8'hEF,        
    parameter pRTOChrDlyCnt = 3,		// Default Receive Time Out Character Delay Count

    // FIFO Configuration Parameters
    parameter pTF_Depth = 2,                	// Tx FIFO Depth: 2**(TF_Depth + 4)
    parameter pRF_Depth = 2,                	// Rx FIFO Depth: 2**(RF_Depth + 4)
    parameter pTF_Init  = "Src/UART_TF.coe",    // Tx FIFO Memory Initialization
    parameter pRF_Init  = "Src/UART_RF.coe"     // Rx FIFO Memory Initialization
)(
    input   Rst,                    // System Reset
    input   Clk,                    // System Clock
    
    //  SSP Interface
    input   SSP_SSEL,               // SSP Slave Select
    input   SSP_SCK,                // Synchronous Serial Port Serial Clock
    input   [2:0] SSP_RA,           // SSP Register Address
    input   SSP_WnR,                // SSP Command
    input   SSP_En,                 // SSP Start Data Transfer Phase (Bits 11:0)
    input   SSP_EOC,                // SSP End-Of-Cycle (Bit 0)
    input   [11:0] SSP_DI,          // SSP Data In
    input   [11:0] SSP_DO,          // SSP Data Out
    
    //  External UART Interface
    input  TxD_232,                // RS-232 Mode TxD
    input  RxD_232,                // RS-232 Mode RxD
    input  xRTS,                   // RS-232 Mode RTS (Ready-To-Receive)
    input  xCTS,                   // RS-232 Mode CTS (Okay-To-Send)
    input  TxD_485,                // RS-485 Mode TxD
    input  RxD_485,                // RS-485 Mode RxD
    input  xDE,                    // RS-485 Mode Transceiver Drive Enable

    //  External Interrupt Request
    input  IRQ,	                // Interrupt Request
    
    //  TxSM/RxSM Status
    input  TxIdle,
    input  RxIdle,
    
    /////// DEBUG /////
    input [7:0] TDR,
    input [11:0] RDR,
    input [11:0] USR,
    input [11:0] UCR,
    input [11:0] SPR,
    input RF_HF
);

wire ssp_write;
assign ssp_write = SSP_SSEL & SSP_WnR & SSP_EOC;
//ssp_ssel_correctness: assert property (@(posedge Clk) SSP_SSEL == 1'b0 |-> SSP_DO == 12'b0); 

// VERIFY SSP and EXTERNAL UART INTERFACE 
assume_write: assume property (@(posedge SSP_SCK) ssp_write == 1'b1);
txd485_high:  assert property (@(posedge SSP_SCK) disable iff (Rst) ~UCR[11] |-> TxD_485); 
txd232_high:  assert property (@(posedge SSP_SCK) disable iff (Rst) UCR[11] |-> TxD_232); 
rs232_xDE:    assert property (@(posedge SSP_SCK) disable iff (Rst) ~UCR[11] |-> ~xDE);
rs485_xDE:    assert property (@(posedge SSP_SCK) disable iff (Rst) UCR[11] |-> xDE == ~TxIdle);
mode0_xRTS:  assert property (@(negedge SSP_SCK) disable iff (Rst) ssp_write & SSP_RA == 3'b000 & SSP_DI[11:9] == 3'b001 |=> xRTS);
mode1_xRTS:  assert property (@(posedge SSP_SCK) disable iff (Rst) UCR[11:10] == 2'b01 & ~RF_HF |-> xRTS);
mode2_xDE:   assert property (@(posedge SSP_SCK) disable iff (Rst) UCR[11:10] == 2'b10 & ~TxIdle |-> xDE);
mode3_xDE:   assert property (@(posedge SSP_SCK) disable iff (Rst) UCR[11:10] == 2'b11 & ~TxIdle |-> xDE);
clear_RFC_TFC: assert property (@(posedge Clk) disable iff (Rst) SSP_EOC & SSP_RA == 3'b010 & ssp_write |-> ~SSP_DO[11] & ~SSP_DO[10]); 
CTSi_check: assert property (@(posedge SSP_SCK) (UCR[11:10] == 2'b01) |=> USR[8] == $past(xCTS,1) );

// VERIFY UCR 
// BR[3:0]  verified by FPGA prototyping 
// FMT[3:0] verified by TXSM and RXSM assertions
IE_check:   assert property (@(posedge Clk) ~UCR[8] & ~IRQ |=> ~IRQ);
// RTSo     verified by mode0_xRTS assertion
genvar i;
for(i=0; i<4; i++) begin
    MD_check: assert property (@(negedge SSP_SCK) disable iff (Rst) ssp_write & SSP_RA == 3'b000 & SSP_DI[11:10] == i |=> USR[11:10] == i);
end
 
reg [3:0] count_modes = 0;
always@(*) begin
    case(USR[11:9])
    0: count_modes[0] = 1'b1;
    1: count_modes[1] = 1'b1;
    2: count_modes[2] = 1'b1;
    3: count_modes[3] = 1'b1;
    default: count_modes = count_modes;
    endcase
end
//cover_modes: cover property (@(posedge Clk) $countones(count_modes == 4));

endmodule 

module wrapper_ssp_uart;

// RTL module VIP module Instance_Name
// .VIP Port (RTL Port) 
bind SSP_UART ssp_uart_props
#(
    .pPS_Default(pPS_Default),
    .pDiv_Default(pDiv_Default),
    .pRTOChrDlyCnt(pRTOChrDlyCnt),
    .pTF_Depth(pTF_Depth),
    .pRF_Depth(pRF_Depth)

)   uart_inst1 (
    .Rst(Rst),
    .Clk(Clk),
    .SSP_SSEL(SSP_SSEL),
    .SSP_SCK(SSP_SCK),
    .SSP_RA(SSP_RA),
    .SSP_WnR(SSP_WnR),
    .SSP_En(SSP_En),
    .SSP_EOC(SSP_EOC),
    .SSP_DI(SSP_DI),
    .SSP_DO(SSP_DO),
    .TxD_232(TxD_232),
    .RxD_232(RxD_232),
    .xRTS(xRTS),
    .xCTS(xCTS),
    .TxD_485(TxD_485),
    .RxD_485(RxD_485),
    .xDE(xDE),
    .IRQ(IRQ),
    .TxIdle(TxIdle),
    .RxIdle(RxIdle),
    .TDR(TDR),
    .RDR(RDR),
    .USR(USR),
    .UCR(UCR),
    .SPR(SPR),
    .RF_HF(RF_HF)
);

endmodule 
