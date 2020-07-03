#TCL file for JasperGold Verification of DPSFnmCE.v (FIFO) 
clear -all 
analyze -v2k DPSFnmCE.v
analyze -sv v_fifo.sv 
elaborate -top DPSFnmCE 
clock Clk
reset Rst
prove -bg -all 
