`timescale 1ns / 1ps
`define  ALUOp_add  5'b00001
`define  ALUOp_sub  5'b00010
`define dm_word 3'b000
`define dm_halfword 3'b001
`define dm_halfword_unsigned 3'b010
`define dm_byte 3'b011
`define dm_byte_unsigned 3'b100
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 2024/11/23 14:32:40
// Design Name: 
// Module Name: sccomp
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module sccomp(
    input clk,
    input rstn,
    input[15:0] sw_i,
    output[7:0] disp_seg_o,
    output[7:0] disp_an_o
    );
    reg[31:0]clkdiv;
    wire Clk_CPU;
    
    always@(posedge clk or negedge rstn )begin
        if(!rstn )clkdiv<=0;
        else clkdiv<=clkdiv+1'b1;end
        
    assign Clk_CPU=(sw_i[15])?clkdiv[27]:clkdiv[25];
    
    reg[63:0]display_data;
reg[5:0]rom_addr;
reg[63:0]led_disp_data;
parameter LED_DATA_NUM=12;
wire [31:0]instr;
reg[31:0]reg_data;//regvalue
reg[31:0]alu_disp_data;
reg[31:0]dmem_data;
reg[5:0]reg_addr;
reg[2:0]alu_addr;
reg[3:0]dmem_addr;
parameter DM_DATA_NUM=16;
wire RegWrite=sw_i[2];
wire [2:0]WD=sw_i[7:5];
wire [2:0]rd=sw_i[10:8];
wire [2:0]rs1=sw_i[10:8];
wire [2:0]rs2=sw_i[7:5];
wire [1:0]ALUOp=sw_i[4:3];
wire MemWrite;
wire [8:0]dm_addr;
wire [1:0]DMType;

dist_mem_im U_IM(.a(rom_addr),.spo(instr));
RF U_RF(.clk(Clk_CPU),.rst(rstn),.RFWr(RegWrite),.sw_i(sw_i),.A1(rs1),.A2(rs2),.A3(rd),.WD(WD),.RD1(RD1),.RD2(RD2));
alu U_alu(.A(U_RF.rf[rs1]),.B(U_RF.rf[rs2]),.ALUOp(ALUOp),.C(aluout),.Zero(Zero));
dm U_DM(.clk(Clk_CPU),.rstn(rstn),.DMWr(MemWrite),.addr(dm_addr[8:0]),.din(dm_din),.DMType(DMType[1:0]),.sw_i(sw_i),.dout(dm_dout));

//产生LED_DATA
always@(posedge Clk_CPU or negedge rstn)begin
if(!rstn)begin rom_addr=6'd0;led_disp_data=64'b1;reg_addr=6'b0;alu_addr=3'b0; end
else if(sw_i[14]==1'b1)begin
    if(rom_addr==LED_DATA_NUM) begin rom_addr=6'd0;led_disp_data=64'b1;end
    else if(sw_i[1])begin rom_addr=rom_addr;end
    else begin rom_addr=rom_addr+1;end
    end
else if(sw_i[13]==1'b1)begin
    reg_addr=reg_addr+1'b1;
    reg_data=U_RF.rf[reg_addr];
    end
else if(sw_i[12]==1'b1)begin
    alu_addr=alu_addr+1'b1;
    case(alu_addr)
    3'b001:alu_disp_data=U_alu.A;
    3'b010:alu_disp_data=U_alu.B;
    3'b011:alu_disp_data=U_alu.C;
    3'b100:alu_disp_data=U_alu.Zero;
    default:alu_disp_data=32'hFFFFFFFF;
    endcase
end
else if(sw_i[11]==1'b1)begin
    dmem_addr = dmem_addr +1'b1;
    dmem_data = U_DM.dmem[dmem_addr][7:0];
    if(dmem_addr == DM_DATA_NUM)begin
        dmem_addr = 6'd0;
        dmem_data = 32'hffffffff;
    end
end
end

//choose display source data
always@(sw_i)begin
    if(sw_i[0]==0)begin
    case(sw_i[14:11])
        4'b1000:display_data=instr;
        4'b0100:display_data=reg_data;
        4'b0010:display_data=alu_disp_data;
        4'b0001:display_data=dmem_data;
        default:display_data=instr;
        endcase end
    else begin display_data=led_disp_data;end
    end
    
    seg7x16 u_seg7x16(
    .clk(clk),
    .rstn(rstn),
    .i_data(display_data),
    .disp_mode(sw_i[0]),
    .o_seg(disp_seg_o),
    .o_sel(disp_an_o)
    );
    
endmodule


//七段码
module seg7x16(
    input clk,
    input rstn,
    input disp_mode,//0,digit;1,graph
    input [63:0]i_data,
    output [7:0]o_seg,
    output[7:0]o_sel
    );
    reg[14:0]cnt;
    wire seg7_clk;
    always@(posedge clk,negedge rstn)
    if(!rstn)
        cnt<=0;
    else
        cnt<=cnt+1'b1;
        
    assign seg7_clk=cnt[14];
    reg[2:0]seg7_addr;
    
    always@(posedge seg7_clk,negedge rstn)
        if(!rstn)
            seg7_addr<=0;
        else
            seg7_addr<=seg7_addr+1'b1;
            
    reg [7:0]o_sel_r;
    
    always@(*)
        case(seg7_addr)
            7:o_sel_r=8'b01111111;
            6:o_sel_r=8'b10111111;
            5:o_sel_r=8'b11011111;
            4:o_sel_r=8'b11101111;
            3:o_sel_r=8'b11110111;
            2:o_sel_r=8'b11111011;
            1:o_sel_r=8'b11111101;
            0:o_sel_r=8'b11111110;
        endcase
        reg [63:0]i_data_store;
        always@(posedge clk,negedge rstn)
            if(!rstn)
                i_data_store<=0;
            else
                i_data_store<=i_data;
                
        reg[7:0]seg_data_r;
        always@(*)
            if(disp_mode==1'b0)begin
            case(seg7_addr)
                0:seg_data_r=i_data_store[3:0];
                1:seg_data_r=i_data_store[7:4];
                2:seg_data_r=i_data_store[11:8];
                3:seg_data_r=i_data_store[15:12];
                4:seg_data_r=i_data_store[19:16];
                5:seg_data_r=i_data_store[23:20];
                6:seg_data_r=i_data_store[27:24];
                7:seg_data_r=i_data_store[31:28];
            endcase end
            else begin
            case(seg7_addr)
                0:seg_data_r=i_data_store[7:0];
                1:seg_data_r=i_data_store[15:8];
                2:seg_data_r=i_data_store[23:16];
                3:seg_data_r=i_data_store[31:24];
                4:seg_data_r=i_data_store[39:32];
                5:seg_data_r=i_data_store[47:40];
                6:seg_data_r=i_data_store[55:48];
                7:seg_data_r=i_data_store[63:56];
            endcase end    
       reg[7:0]o_seg_r;
       always@(posedge clk,negedge rstn)
            if(!rstn)
                o_seg_r<=8'hff;
            else if(disp_mode==1'b0)begin
                case(seg_data_r)
                4'h0:o_seg_r<=8'hC0;
                4'h1:o_seg_r<=8'hF9;
                4'h2:o_seg_r<=8'hA4;
                4'h3:o_seg_r<=8'hB0;
                4'h4:o_seg_r<=8'h99;
                4'h5:o_seg_r<=8'h92;
                4'h6:o_seg_r<=8'h82;
                4'h7:o_seg_r<=8'hF8;
                4'h8:o_seg_r<=8'h80;
                4'h9:o_seg_r<=8'h90;
                4'hA:o_seg_r<=8'h88;
                4'hB:o_seg_r<=8'h83;
                4'hC:o_seg_r<=8'hC6;
                4'hD:o_seg_r<=8'hA1;
                4'hE:o_seg_r<=8'h86;
                4'hF:o_seg_r<=8'h8E;
                endcase end
                else begin o_seg_r<=seg_data_r;end
                
        assign o_sel=o_sel_r;
        assign o_seg=o_seg_r;
endmodule

module RF( 
    input	clk,						//分频后的主时钟 CLK
    input	rst,							//reset signal
    input	RFWr,						//Rfwrite = mem2reg  
    input 	[15:0] sw_i, 		 		//sw_i[15]---sw_i[0]
    input 	[4:0] A1, A2, A3,		// Register Num 
    input 	[31:0] WD,					//Write data
    output reg[31:0] RD1, RD2	//Data output port
); 
    reg [31:0]rf[31:0];
    integer i;
    always@(posedge clk or negedge rst)begin
    if(!rst)begin
        for(i=0;i<32;i=i+1)
            begin
            rf[i]<=i;
            end
    end
    else if(RFWr&&(!sw_i[1]))begin
                rf[A3]<=WD;
                end
    RD1=(A1!=0)?rf[A1]:0;
    RD2=(A2!=0)?rf[A2]:0;
    end

endmodule

module alu( 
input signed [31:0] A, B,  //alu input num
input [4:0]  ALUOp, //alu how to do 
output reg signed [31:0] 	C, // alu result 
output reg  Zero
); 
    always@(*)begin
        case(ALUOp)
        `ALUOp_add:C=A+B;
        `ALUOp_sub:C=A-B;
        endcase
        Zero=(C==0)?1:0;
    end
endmodule

module dm( 
input clk, //100MHZ CLK
input rstn,
input DMWr, //write signal
input [5:0] addr,
input [31:0] din,
input [2:0] DMType, 
input [15:0]sw_i,
output reg [31:0] dout 
); 
reg [7:0] dmem[127:0];
integer i;
always@(posedge clk or negedge rstn) begin
    if(!rstn) begin
        for(i=0;i<128;i=i+1)
            begin
            dmem[i]<=i;
            end
    end
    else if(clk && sw_i[1]==0) begin
        case(DMType)
            `dm_byte:dmem[addr]<=din[7:0];
            `dm_halfword:begin
                dmem[addr]<=din[7:0];
                dmem[addr+1]<=din[15:8];
            end
            `dm_word:begin
                dmem[addr]<=din[7:0];
                dmem[addr+1]<=din[15:8];
                dmem[addr+2]<=din[23:16];
                dmem[addr+3]<=din[31:24];
            end
        endcase
    end
end
always@(*) begin
    case(DMType)
        `dm_byte:dout={{24{dmem[addr][7]}},dmem[addr][7:0]};
        `dm_halfword:dout={{16{dmem[addr][7]}},dmem[addr+1][7:0],dmem[addr][7:0]};
        `dm_word:dout={dmem[addr+3][7:0],dmem[addr+2][7:0],dmem[addr+1][7:0],dmem[addr][7:0]};
        default:dout=32'hffffffff;
    endcase
end
endmodule
