module RXSM_props (
    input Rst,
    input Clk,
    input CE_16x,
    input Len,
    input NumStop,
    input ParEn,
    input [1:0] Par,
    input RxD,
    input [8:0] RD,
    input WE_RHR,
    input RxWait,
    input RxIdle,
    input RxStart,
    input RxShift,
    input RxParity,
    input RxStop,
    input RxError,
    input CE_RxSM,
    input ParErr
);

wire Odd, Even;
//assign Odd = ^{RxD,RSR};
assign Even = ~Odd;

//always@(*) begin
  //  case(Par)
//end
reset_values:       assert property (@(posedge Clk) $past(Rst,1) |=> RD == 9'b0 & RxWait);

wait_transition:   assert property (@(posedge Clk) disable iff (Rst) RxError & CE_RxSM |=> RxWait);
idle_transition:   assert property (@(posedge Clk) disable iff (Rst) RxIdle & CE_RxSM & RxD |=> RxIdle);
start_transition:  assert property (@(posedge Clk) disable iff (Rst) RxIdle & ~RxD & CE_RxSM |=> RxStart);
shift0_transition: assert property (@(posedge Clk) disable iff (Rst) RxStart & ~RxD & CE_RxSM |=> RxShift);
shift_transitions: assert property (@(posedge Clk) disable iff (Rst) $rose(RxShift) |-> RxShift[->7]);
parity_transition: assert property (@(posedge Clk) disable iff (Rst) RxParity & $past(CE_RxSM,1) |-> $past(RxShift,1));
stop_transition:   assert property (@(posedge Clk) disable iff (Rst) RxParity & ~ParErr & CE_RxSM |=> RxStop);
error_transition:  assert property (@(posedge Clk) disable iff (Rst) RxStop  & ~RxD & CE_RxSM |=> RxError);

WE_RHR_correct:    assert property (@(posedge Clk) disable iff (Rst) (~CE_RxSM | (~RxD & ~RxError)) |=> ~WE_RHR);
NumStop_correct:   assert property (@(posedge Clk) disable iff (Rst) $rose(RxStop) & NumStop |=> RxStop);
//Len_correct:       assert property (@(posedge Clk) disable iff (Rst) $rose(RxShift) ##1 CE_RxSM[->6] ##16
 //   								     (CE_RxSM & ~Len & RxShift) |=> RxShift); 
ParEn_correct:     assert property (@(posedge Clk) disable iff (Rst) RxShift & ~ParEn & ~Len |=> ~RxParity);
ParErr_correct:    assert property (@(posedge Clk) disable iff (Rst) ~RxParity |-> ~ParErr);

count_RxWait:   cover property(@(posedge Clk) disable iff (Rst) RxWait);
count_RxIdle:   cover property(@(posedge Clk) disable iff (Rst) RxIdle);
count_RxStart:  cover property(@(posedge Clk) disable iff (Rst) RxStart);
count_RxShift:  cover property(@(posedge Clk) disable iff (Rst) RxShift);
count_RxParity: cover property(@(posedge Clk) disable iff (Rst) RxParity);
count_RxStop:   cover property(@(posedge Clk) disable iff (Rst) RxStop);
count_RxError:  cover property(@(posedge Clk) disable iff (Rst) RxError);

endmodule 

module wrapper_rxsm;

bind UART_RXSM RXSM_props rxsm_inst1 (
    .Rst(Rst),
    .Clk(Clk),
    .CE_16x(CE_16x),
    .Len(Len),
    .NumStop(NumStop),
    .ParEn(ParEn),
    .Par(Par),
    .RxD(RxD),
    .RD(RD),
    .WE_RHR(WE_RHR),
    .RxWait(RxWait),
    .RxIdle(RxIdle),
    .RxStart(RxStart),
    .RxShift(RxShift),
    .RxParity(RxParity),
    .RxStop(RxStop),
    .RxError(RxError),
    .CE_RxSM(CE_RxSM),
    .ParErr(ParErr)
);

endmodule
