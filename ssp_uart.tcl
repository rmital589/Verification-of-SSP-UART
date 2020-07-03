clear -all 
analyze -v2k DPSFnmCE.v
analyze -v2k fedet.v
analyze -v2k re1ce.v 
analyze -v2k redet.v
analyze -v2k UART_BRG.v
analyze -v2k UART_INT.v
analyze -v2k UART_RTO.v
analyze -v2k UART_RXSM.v
analyze -v2k UART_TXSM.v
analyze -v2k SSP_UART.v 

analyze -sv v_SSP_UART.sv 
analyze -sv v_UART_TXSM.sv
analyze -sv v_UART_RXSM.sv

elaborate -top SSP_UART
#clock SSP_SCK -both_edges
clock Clk
reset Rst
prove -bg -all 
