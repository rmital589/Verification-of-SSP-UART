

//Sysemverilog properties for UART_TXSM

module UART_TXSM_props(
	input Rst,
	input Clk,

	input CE_16x,

	input Len,
	input NumStop,
	input ParEn,
	input [1:0] Par,
	
	input TF_EF,
	
	input [7:0] THR,
	input TF_RE,
	
	input CTSi,

	input TxD,

	input [3:0] TxSM,
	input CE_TxSM,
	input Ld_TSR,

	input TxIdle,
	input TxStart,
	input TxShift,
	input TxStop
);

localparam  pIdle       =  0;   // Idle  - wait for data
localparam  pStopDelay  =  1;   // Stop  - deassert DE/RTS after 1 bit delay
localparam  pStartDelay =  2;   // Start - assert DE/RTS, delay 1 bit & CTSi
localparam  pUnused     =  3;   // Unused State
localparam  pStartBit   = 10;   // Shift - transmit Start Bit
localparam  pShift0     = 11;   // Shift - transmit TSR contents (LSB)
localparam  pShift1     =  9;   // Shift - transmit TSR contents
localparam  pShift2     =  8;   // Shift - transmit TSR contents
localparam  pShift3     = 12;   // Shift - transmit TSR contents
localparam  pShift4     = 13;   // Shift - transmit TSR contents
localparam  pShift5     = 15;   // Shift - transmit TSR contents
localparam  pShift6     = 14;   // Shift - transmit TSR contents
localparam  pShift7     =  6;   // Shift - transmit TSR contents (MSB)
localparam  pParityBit  =  4;   // Shift - transmit Parity Bit
localparam  pStopBit2   =  5;   // Shift - transmit Stop Bit 1
localparam  pStopBit1   =  7;   // Shift - transmit Stop Bit 2

reg [11:0] TSR;
reg [7:0] TxData;

reg [3:0] TxSM_d;
reg parity;

always @(posedge Clk) begin
	if (Rst) begin
		TSR <= 0;
		TxSM_d <= 0;
		parity <= 0;
	end

	else begin
		TxSM_d <= TxSM;
		if (Ld_TSR) begin
			TxData <= THR;
			case(Par)
				2'b00: parity <= Len ? ~(^THR[6:0]) : ~(^THR);
				2'b01: parity <= Len ? ^THR[6:0] : ^THR;
				2'b10: parity <= 0;
				2'b11: parity <= 1;
			endcase
		end
		if (TxSM_d == pStartBit) TSR[0] <= TxD;
		if (TxSM_d == pShift0)   TSR[1] <= TxD;
		if (TxSM_d == pShift1)   TSR[2] <= TxD;
		if (TxSM_d == pShift2)   TSR[3] <= TxD;
		if (TxSM_d == pShift3)   TSR[4] <= TxD;
		if (TxSM_d == pShift4)   TSR[5] <= TxD;
		if (TxSM_d == pShift5)   TSR[6] <= TxD;
		if (TxSM_d == pShift6)   TSR[7] <= TxD;
		if (TxSM_d == pShift7)   TSR[8] <= TxD;
		if (TxSM_d == pParityBit)   TSR[9] <= TxD;
		if (TxSM_d == pStopBit2)   TSR[10] <= TxD;
		if (TxSM_d == pStopBit1)   TSR[11] <= TxD;
	end
end


//Assume
assume property(@(posedge Clk) disable iff(Rst) CE_16x |-> ##1 !CE_16x);

//FSM Transition Assertions
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle) && CE_TxSM && !TF_EF |-> ##1 (TxSM == pStartDelay));
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle) && TF_EF && CE_TxSM |-> ##1 TxSM == pIdle);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStartDelay) && TF_EF && CE_TxSM |-> ##1 TxSM == pIdle);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStartDelay) && !TF_EF && !CTSi && CE_TxSM |-> ##1 TxSM == pStartDelay);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStartDelay) && !TF_EF && CTSi && CE_TxSM |-> ##1 TxSM == pStartBit);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStartBit) && CE_TxSM |-> ##1 TxSM == pShift0);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift0) && CE_TxSM |-> ##1 TxSM == pShift1);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift1) && CE_TxSM |-> ##1 TxSM == pShift2);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift2) && CE_TxSM |-> ##1 TxSM == pShift3);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift3) && CE_TxSM |-> ##1 TxSM == pShift4);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift4) && CE_TxSM |-> ##1 TxSM == pShift5);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift5) && CE_TxSM |-> ##1 TxSM == pShift6);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift6) && !Len && CE_TxSM |-> ##1 TxSM == pShift7);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift6) && Len && CE_TxSM |-> ##1 TxSM == pParityBit);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift7) && ParEn && CE_TxSM |-> ##1 TxSM == pParityBit);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift7) && !ParEn && NumStop && CE_TxSM |-> ##1 TxSM == pStopBit2);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pShift7) && !ParEn && !NumStop && CE_TxSM |-> ##1 TxSM == pStopBit1);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pParityBit) && NumStop && CE_TxSM |-> ##1 TxSM == pStopBit2);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pParityBit) && !NumStop && CE_TxSM |-> ##1 TxSM == pStopBit1);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStopBit2) && CE_TxSM |-> ##1 TxSM == pStopBit1);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStopBit1) && TF_EF && CE_TxSM |-> ##1 TxSM == pStopDelay);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStopBit1) && !TF_EF && CE_TxSM |-> ##1 TxSM == pStartBit);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStopDelay) && TF_EF && CE_TxSM |-> ##1 TxSM == pIdle);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStopDelay) && !TF_EF && !CTSi && CE_TxSM |-> ##1 TxSM == pStartDelay);
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pStopDelay) && !TF_EF && CTSi && CE_TxSM |-> ##1 TxSM == pStartBit);

//Read Enable
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle) |-> ##1 !TF_RE);
assert property(@(posedge Clk) disable iff(Rst) !CTSi || TF_EF |-> ##1 !TF_RE);


//TxD
assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle && !TF_EF && CE_TxSM) ##1 !CE_TxSM[*0:$] ##1 (!TF_EF && CTSi && CE_TxSM) ##1 CE_TxSM[->9] |->
						 ##1 (TSR[0] == 0) && (TSR[7:1] == TxData[6:0]));

assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle && !TF_EF && CE_TxSM) ##1 !CE_TxSM[*0:$] ##1 (!TF_EF && CTSi && CE_TxSM) ##1 CE_TxSM[->7] ##1 !CE_TxSM[*0:$] ##1 CE_TxSM && !Len|->
                                                 ##3 (TSR[8] == TxData[7]));

assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle && !TF_EF && CE_TxSM) ##1 !CE_TxSM[*0:$] ##1 (!TF_EF && CTSi && CE_TxSM) ##1 CE_TxSM[->7] ##1 !CE_TxSM[*0:$] ##1 CE_TxSM && !Len
                                                 ##1 !CE_TxSM[*0:$] ##1 CE_TxSM && ParEn |-> ##3 (TSR[9] == parity));


assert property(@(posedge Clk) disable iff(Rst) (TxSM == pIdle && !TF_EF && CE_TxSM) ##1 !CE_TxSM[*0:$] ##1 (!TF_EF && CTSi && CE_TxSM) ##1 CE_TxSM[->7] ##1 !CE_TxSM[*0:$] ##1 CE_TxSM && !Len
                                                 ##1 !CE_TxSM[*0:$] ##1 CE_TxSM && ParEn |-> ##3 (TSR[9] == parity));


//Cover
cover property(@(posedge Clk) disable iff(Rst) TF_RE);
cover property(@(posedge Clk) disable iff(Rst) !TF_EF);
cover property(@(posedge Clk) disable iff(Rst) TxSM == pStartBit);
cover property(@(posedge Clk) disable iff(Rst) TxD);
cover property(@(posedge Clk) disable iff(Rst) !TxD);
cover property(@(posedge Clk) disable iff(Rst) Len);
cover property(@(posedge Clk) disable iff(Rst) !Len);
cover property(@(posedge Clk) disable iff(Rst) ParEn);
cover property(@(posedge Clk) disable iff(Rst) Par == 2'b00);
cover property(@(posedge Clk) disable iff(Rst) Par == 2'b01);
cover property(@(posedge Clk) disable iff(Rst) Par == 2'b10);
cover property(@(posedge Clk) disable iff(Rst) Par == 2'b11);
cover property(@(posedge Clk) disable iff(Rst) CTSi);

endmodule

module Wrapper_txsm;

bind UART_TXSM UART_TXSM_props UART_TXSM_bind(
	.Rst(Rst),
	.Clk(Clk),
	.CE_16x(CE_16x),
	.Len(Len),
	.NumStop(NumStop),
	.ParEn(ParEn),
	.Par(Par),
	.TF_EF(TF_EF),
	.THR(THR),
	.TF_RE(TF_RE),
	.CTSi(CTSi),
	.TxD(TxD),
	.TxSM(TxSM),
	.CE_TxSM(CE_TxSM),
	.Ld_TSR(Ld_TSR),
	.TxIdle(TxIdle),
	.TxStart(TxStart),
	.TxShift(TxShift),
	.TxStop(TxStop)
);

endmodule
