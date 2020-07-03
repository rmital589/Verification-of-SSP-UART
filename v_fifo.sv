// Properties for DPSFnmCE verification 
module fifo_props #(
    parameter addr = 4,
    parameter width = 16

)(
    input Rst,
    input Clk,
    input WE,
    input RE,
    input [(width-1):0] DI,
    input [(width-1):0] DO,
    input FF,
    input EF,
    input HF,
    input [addr:0] Cnt
);

reg [addr-1:0] wr_ptr;
reg [addr-1:0] rd_ptr;
reg [2**addr-1:0] used;
reg [addr:0] push_cnt, pop_cnt;
always@(posedge Clk or posedge Rst) begin
    if(Rst) 
	begin
	wr_ptr <= 0; 
   	rd_ptr <= 0; 
	used <= 0;
        pop_cnt <= 0; 
	push_cnt <= 0;
        end
    else if(~FF & WE) 
	begin
	wr_ptr <= wr_ptr + 1'b1; 
	used[wr_ptr] <= 1'b1;
  	push_cnt <= push_cnt + 1'b1;
	end
    else if(~EF & RE) 
	begin
	rd_ptr <= rd_ptr + 1'b1; 
	used[rd_ptr] <= 1'b0;
        pop_cnt <= pop_cnt + 1'b1;
	end 
    else 
	begin
	wr_ptr <= wr_ptr; rd_ptr <= rd_ptr; used <= used;
	end
end

// Assume
assume_WE_RE: assume property (@(posedge Clk) !(WE & RE));

// Assert
empty_correct: assert property (@(posedge Clk) $countones(used) == 0 |-> EF);
half_full_correcnt: assert property (@(posedge Clk) $countones(used) >= ((2**addr)/2) |->  HF);
full_correct: assert property (@(posedge Clk) $countones(used) == (2**addr) |-> FF);
count_correct: assert property (@(posedge Clk) Cnt == $countones(used));

// Cover  
genvar i;
for (i=0; i < 2**addr; i++) begin
    //all_used: cover property ( $countones(used) == i);
end 
genvar j;
for (j=0; j < 2**addr ; j++) begin 
//    wr_num: cover property ( push_cnt == j);
//    rd_num: cover property ( pop_cnt == j);
end 

endmodule 

module wrapper_fifo;

bind DPSFnmCE fifo_props 
#(
    .addr(addr),
    .width(width)
    
) fifo_inst1(
    .Rst(Rst),
    .Clk(Clk), 
    .WE(WE),
    .RE(RE),
    .DI(DI),
    .DO(DO),
    .FF(FF),
    .EF(EF),
    .HF(HF),
    .Cnt(Cnt)
    );

endmodule 
