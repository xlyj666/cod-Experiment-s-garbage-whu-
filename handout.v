// NPC control signal
`define NPC_PLUS4   3'b000
`define NPC_BRANCH  3'b001
`define NPC_JUMP    3'b010
`define NPC_JALR 3'b100

// ALU control signal
`define ALU_NOP   3'b000 
`define ALU_ADD   3'b001
`define ALU_SUB   3'b010 
`define ALU_AND   3'b011
`define ALU_OR    3'b100

//EXT CTRL itype, stype, btype, utype, jtype
`define EXT_CTRL_ITYPE_SHAMT 6'b100000
`define EXT_CTRL_ITYPE	6'b010000
`define EXT_CTRL_STYPE	6'b001000
`define EXT_CTRL_BTYPE	6'b000100
`define EXT_CTRL_UTYPE	6'b000010
`define EXT_CTRL_JTYPE	6'b000001

`define GPRSel_
`define GPRSel_RD 2'b00RT 2'b01
`define GPRSel2'b10

`define WDSel_From_31 ALU 2'b00
`define WDSel_FromMEM 2'b01
`define WDSel_FromPC 2'b10

`define ALUOp_nop 5'b00000
`define ALUOp_lui 5'b00001
`define ALUOp_auipc 5'b00010
`define ALUOp_add 5'b00011
`define ALUOp_sub 5'b00100
`define ALUOp_bne 5'b00101
`define ALUOp_bfine ALUOp_'b01000
`define ALUOp_blt 5'b00110
`degeubge 5'b00111
`define ALUOp_bltu 5 5'b01001
`define ALUOp_slt 5'b01010
`define ALUOp_sltu 5'b01011
`define ALUOp_xor 5'b01100
`define ALUOp_or 5'b01101
`define ALUOp_and 5'b01110
`define ALUOp_sll 5'b01111
`define ALUOp_srl 5'b10000
`define ALUOp_sra 5'b10001
`define ALUOp_jalr 5'b10010

`define dm_word 3'b000
`define dm_halfword 3'b001
`define dm_halfword_unsigned 3'b010
`define dm_byte 3'b011
`define dm_byte_unsigned 3'b100

module cpu(
    input clk,
    input rstn,
    input[15:0] sw_i,
    output[7:0] disp_seg_o,
    output[7:0] disp_an_o,


    output[15:0] led_o //new

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
wire [31:0]inst_in;
reg[31:0]reg_data;//regvalue
reg[31:0]alu_disp_data;
reg[31:0]dmem_data;
reg[5:0]reg_addr;
reg[2:0]alu_addr;
wire        ALUSrc;      // ALU source for A
wire        Zero;        // ALU ouput zero
reg[3:0]dmem_addr;
parameter DM_DATA_NUM=16;

wire [2:0]rd;
wire [2:0]rs1;
wire [2:0]rs2;
wire        RegWrite;    // control signal to register write
wire [5:0]       EXTOp;       // control signal to signed extension
wire [4:0]  ALUOp;       // ALU opertion
wire [2:0]  NPCOp;       // next PC operation
wire [1:0]  WDSel;       // (register) write data selection
wire MemWrite;
wire [31:0]    dm_addr, dm_din, dm_dout;
wire [1:0]DMType;
wire [4:0] iimm_shamt;
wire [11:0] iimm,simm,bimm;
wire [19:0] uimm,jimm;
wire [31:0] immout;
wire[31:0] aluout;
wire [6:0]  Op;          // opcode
wire [6:0]  Funct7;       // funct7
wire [2:0]  Funct3;       // funct3
wire [11:0] Imm12;       // 12-bit immediate
wire [31:0] Imm32;       // 32-bit immediate
wire [19:0] IMM;         // 20-bit immediate (address)
reg [31:0] WD;          // register write data
wire [31:0] RD1,RD2;         // register data specified by rs
wire [31:0] B;           // operator for ALU B
assign Addr_out=aluout;
assign B = (ALUSrc) ? immout : RD2; // immout from EXT is immediate generated
assign Data_out = RD2;//删
assign iimm_shamt=inst_in[24:20];
assign bimm={inst_in[31],inst_in[7],inst_in[30:25],inst_in[11:8]};
assign uimm=inst_in[31:12];
assign jimm={inst_in[31],inst_in[19:12],inst_in[20],inst_in[30:21]};
assign Op = inst_in[6:0];  // instruction
assign Funct7 = inst_in[31:25]; // funct7
assign Funct3 = inst_in[14:12]; // funct3
assign rs1 = inst_in[19:15];  // rs1
assign rs2 = inst_in[24:20];  // rs2
assign rd = inst_in[11:7];  // rd
assign iimm=inst_in[31:20];// 12-bit immediate
assign simm = inst_in[31:15][11:7];  // 20-bit immediate

dist_mem_im U_IM(.a(rom_addr),.spo(inst_in));
RF U_RF(.clk(Clk_CPU),.rst(rstn),.write_en(RegWrite), 
		.read_addr_1(rs1), .read_addr_2(rs2), .write_addr(rd), 
		.write_data(WD), 
		.read_data_1(RD1), .read_data_2(RD2));
alu U_alu(.A(RD1),.B(B),.ALUOp(ALUOp),.C(aluout),.Zero(Zero),.PC(PC_out));
dm U_DM(.clk(Clk_CPU),.rstn(rstn),.DMWr(MemWrite),.addr(aluout),.din(RD2),.DMType(DMType[1:0]),.sw_i(sw_i),.dout(dm_dout));
ctrl U_ctrl(.Op(Op), .Funct7(Funct7), .Funct3(Funct3), .Zero(Zero), .RegWrite(RegWrite), .MemWrite(MemWrite),.EXTOp(EXTOp), .ALUOp(ALUOp), .NPCOp(NPCOp), .ALUSrc(ALUSrc), .WDSel(WDSel),.DMType(DMType));
EXT U_EXT(.iimm_shamt(iimm_shamt), .iimm(iimm), .simm(simm), .bimm(bimm),.uimm(uimm), .jimm(jimm),.EXTOp(EXTOp), .immout(immout));
//浜х敓LED_DATA
always @(*)
begin
	case(WDSel)
		`WDSel_FromALU: WD<=aluout;
		`WDSel_FromMEM: WD<=dm_dout;
		`WDSel_FromPC: WD<=PC_out+4;
        default: WD<=aluout;
	endcase

end



always@(*)begin //new
    led_o=16'b00000000;
    if(WD==1) begin led_o[0] <=1 end
    if(RD2==1) begin led_o[1]<=1 end
    if(B==1) begin led_o[2]<=1 end
    if(aluout) begin led_o[3]<=1 end 
    if(rd[0]==0) begin led_o[4]<=1 end
    if(rd[0]==1) begin led_o[5]<=1 end
    if(immout) begin led_o[6]<=1 end
    if(dm_dout) begin led_o[7]<=1 end
    if(WDSel=='WDSel_FromMEM) begin led_o[8]<=1 end//new

    end




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
        4'b1000:display_data=inst_in;
        4'b0100:display_data=reg_data;
        4'b0010:display_data=alu_disp_data;
        4'b0001:display_data=dmem_data;
        default:display_data=inst_in;
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


//涓冩鐮�
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

module RF (
  input wire clk, 
  input wire rst,
  // read enable. In this CPU it doesn't work and always shows 1. 
  // input wire read_en_1,
  // input wire read_en_2,
  input wire write_en,
  input wire [4:0] read_addr_1,
  input wire [4:0] read_addr_2,
  input wire [4:0] write_addr,
  input wire [31:0] write_data,
  output reg [31:0] read_data_1,
  output reg [31:0] read_data_2
);

  wire read_en_1 = 1;
  wire read_en_2 = 1;
  reg [31:0] RegFile[31:0];
  integer i=0;



// write logic
  always @(posedge clk) begin

    if (rst) begin
      for (i=0; i<32; i=i+1) begin
        RegFile[i] <= i;
      end // clear all registers when rst=1
      read_data_1 <= 0;
      read_data_2 <= 0;
    end //clear when rst=1

    else begin
      if (write_en) begin
        if ((read_addr_1 == write_addr)) begin //when read and write at the same register
            read_data_1 <= write_data;
            end
        if ((read_addr_2 == write_addr)) begin //when read and write at the same register
            read_data_2 <= write_data;
            end
        else begin
          RegFile[write_addr] <= write_data;
        end
      end //write data
      RegFile[0] <= 0;
      end
    end


endmodule

module alu( 
input signed [31:0] A, B,  //alu input num
input [4:0]  ALUOp, //alu how to do 
output reg signed [31:0] C, // alu result 
output reg  Zero
); 
    always@(*)begin
        case(ALUOp)
        `ALUOp_nop:C=A;
        `ALUOp_lui:C=B;
        `ALUOp_auipc:C=PC+B;
        `ALUOp_add:C=A+B;
        `ALUOp_sub:C=A-B;
        `ALUOp_bne:C={31'b0,(A==B)};
        `ALUOp_blt:C={31'b0,(A>=B)};
        `ALUOp_bge:C={31'b0,(A<B)};
         `ALUOp_bltu:C={31'b0,($unsigned(A)>=$unsigned(B))};
          `ALUOp_bgeu:C={31'b0,($unsigned(A)<$unsigned(B))};
      `ALUOp_slt:C={31'b0,(A<B)};
        `ALUOp_sltu:C={31'b0,($unsigned(A)<$unsigned(B))};
          `ALUOp_xor:C=A^B;
      `ALUOp_or:C=A|B;
          `ALUOp_and:C=A&B;
        endcase
        assign Zero = (C == 32'b0);

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
reg [31:0] dmem[31:0];
integer i;
always@(posedge clk or negedge rstn) begin
    if(!rstn) begin
        for(i=0;i<128;i=i+1)
            begin
            dmem[i]<=i;
            end
    end
    else if(DMWr && sw_i[1]==0) begin//可以删了sw_i[1]试一试
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

module ctrl(Op, Funct7, Funct3, Zero, 
            RegWrite, MemWrite,
            EXTOp, ALUOp, NPCOp, 
            ALUSrc, WDSel,DMType
            );
            
   input  [6:0] Op;       // opcode
   input  [6:0] Funct7;    // funct7
   input  [2:0] Funct3;    // funct3
   input        Zero;
   
   output       RegWrite; // control signal for register write
   output       MemWrite; // control signal for memory write
   output [5:0] EXTOp;    // control signal to signed extension
   output [4:0] ALUOp;    // ALU opertion
   output [2:0] NPCOp;    // next pc operation
   output       ALUSrc;   // ALU source for A
   output [2:0] DMType;
   output [1:0] WDSel;    // (register) write data selection
   

  // u format
  wire i_lui = ~Op[6]&Op[5]&Op[4]&~Op[3]&Op[2]&Op[1]&Op[0]; //opcode 0110111 
  wire i_auipc = ~Op[6]&~Op[5]&Op[4]&~Op[3]&Op[2]&Op[1]&Op[0]; // opcode 0010111

  // r format
    wire rtype  = ~Op[6]&Op[5]&Op[4]&~Op[3]&~Op[2]&Op[1]&Op[0]; //0110011
    wire i_add  = rtype& ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]&~Funct3[2]&~Funct3[1]&~Funct3[0]; // add 0000000 000
    wire i_sub  = rtype& ~Funct7[6]& Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]&~Funct3[2]&~Funct3[1]&~Funct3[0]; // sub 0100000 000
    wire i_or   = rtype& ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]& Funct3[2]& Funct3[1]&~Funct3[0]; // or 0000000 110
    wire i_and  = rtype& ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]& Funct3[2]& Funct3[1]& Funct3[0]; // and 0000000 111
    wire i_xor = rtype & ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]& Funct3[2]& ~Funct3[1]& ~Funct3[0]; // xor 0000000 100
    wire i_sll = rtype & ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]& ~Funct3[2]& ~Funct3[1]& Funct3[0]; // sll 0000000 001

    wire i_slt = rtype & ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]& ~Funct3[2]& Funct3[1]& ~Funct3[0]; // slt 0000000 010
    wire i_sltu = rtype & ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0]& ~Funct3[2]& Funct3[1]& Funct3[0]; // sltu 0000000 011

  // i format
    wire itype_l  = ~Op[6]&~Op[5]&~Op[4]&~Op[3]&~Op[2]&Op[1]&Op[0]; //0000011
    wire i_lw = itype_l& ~Funct3[2]& Funct3[1]& ~Funct3[0]; // lw 010

  // i format
    wire itype_r  = ~Op[6]&~Op[5]&Op[4]&~Op[3]&~Op[2]&Op[1]&Op[0]; //0010011
    wire i_addi  =  itype_r& ~Funct3[2]& ~Funct3[1]& ~Funct3[0]; // addi 000
    wire i_ori  =  itype_r& Funct3[2]& Funct3[1]&~Funct3[0]; // ori 110

    wire i_andi = itype_r& Funct3[2]& Funct3[1]& Funct3[0]; // andi 111
    wire i_xori = itype_r& Funct3[2]& ~Funct3[1]& ~Funct3[0]; //xori 100
    wire i_slli = itype_r& ~Funct3[2]& ~Funct3[1]& Funct3[0]& ~Funct7[6]&~Funct7[5]&~Funct7[4]&~Funct7[3]&~Funct7[2]&~Funct7[1]&~Funct7[0];  //slli 001 0000000(funct7)
	
   wire i_slti = itype_r& ~Funct3[2]& Funct3[1]& ~Funct3[0];  // slti 010
   wire i_sltiu = itype_r& ~Funct3[2]& Funct3[1]& Funct3[0]; // sltiu 011

  //jalr
	wire i_jalr = Op[6]&Op[5]&~Op[4]&~Op[3]&Op[2]&Op[1]&Op[0]  ; //jalr 1100111 000

  // s format
   wire stype  = ~Op[6]&Op[5]&~Op[4]&~Op[3]&~Op[2]&Op[1]&Op[0];//0100011
   wire i_sw   =  stype& ~Funct3[2]& Funct3[1]&~Funct3[0]; // sw 010

  // sb format
   wire sbtype  = Op[6]&Op[5]&~Op[4]&~Op[3]&~Op[2]&Op[1]&Op[0];//1100011
   wire i_beq  = sbtype& ~Funct3[2]& ~Funct3[1]&~Funct3[0]; // beq 000
   wire i_blt = sbtype& Funct3[2]& ~Funct3[1]&~Funct3[0]; // blt 100
   wire i_bltu = sbtype& Funct3[2]& Funct3[1]&~Funct3[0]; // bltu 110
	
  // j format
   wire i_jal  = Op[6]& Op[5]&~Op[4]& Op[3]& Op[2]& Op[1]& Op[0];  // jal 1101111

  // generate control signals
  assign RegWrite   = rtype | itype_r | i_jalr | i_jal | i_lui | i_auipc | i_sll | i_slli | itype_l; // register write
  assign MemWrite   = stype;                           // memory write
  assign ALUSrc     = itype_r | itype_l | stype | i_jal | i_jalr | i_lui | i_auipc;   // ALU B is from instruction immediate

  // signed extension
  // EXT_CTRL_ITYPE_SHAMT 6'b100000
  // EXT_CTRL_ITYPE	      6'b010000
  // EXT_CTRL_STYPE	      6'b001000
  // EXT_CTRL_BTYPE	      6'b000100
  // EXT_CTRL_UTYPE	      6'b000010
  // EXT_CTRL_JTYPE	      6'b000001
  assign EXTOp[5]    = i_slli;
  assign EXTOp[4]    = (i_jalr | itype_r | itype_l) & (!i_slli);  // not slli instruction cuz its extop5
  assign EXTOp[3]    = stype; 
  assign EXTOp[2]    = sbtype; 
  assign EXTOp[1]    = i_lui | i_auipc;   
  assign EXTOp[0]    = i_jal;         
  
  // write data selection
  // WDSel_FromALU 2'b00
  // WDSel_FromMEM 2'b01
  // WDSel_FromPC  2'b10 
  assign WDSel[0] = itype_l;
  assign WDSel[1] = i_jal | i_jalr;

  // next pc source
  // NPC_PLUS4   3'b000
  // NPC_BRANCH  3'b001
  // NPC_JUMP    3'b010
  // NPC_JALR	   3'b100
  assign NPCOp[0] = sbtype & Zero;
  assign NPCOp[1] = i_jal;
  assign NPCOp[2] = i_jalr;

  // dm_word 3'b000
  //dm_halfword 3'b001
  //dm_halfword_unsigned 3'b010
  //dm_byte 3'b011
  //dm_byte_unsigned 3'b100
  assign DMType[2]=i_lbu;
  assign DMType[1]=i_lb | i_sb | i_lhu;
  assign DMType[0]=i_lh | i_sh | i_lb | i_sb;


  assign ALUOp[0] = itype_l|stype|i_addi|i_ori|i_add|i_or|i_lui|i_slli|i_sll|i_sltu|i_sltiu;
  assign ALUOp[1] = i_jalr|itype_l|stype|i_addi|i_add|i_and|i_auipc|i_andi|i_slli|i_sll|i_sltu|i_slt|i_sltiu|i_slti|i_blt;
  assign ALUOp[2] = i_andi|i_and|i_ori|i_or|i_beq|i_sub|i_xori|i_xor|i_slli|i_sll|i_blt;
  assign ALUOp[3] = i_andi|i_and|i_ori|i_or|i_xori|i_xor|i_slli|i_sll|i_sltu|i_slt|i_sltiu|i_slti|i_bltu;
  assign ALUOp[4] = i_jalr;

endmodule

module EXT( 
	input [4:0] iimm_shamt,
    input	[11:0]			iimm, //instr[31:20], 12 bits
	input	[11:0]			simm, //instr[31:25, 11:7], 12 bits
	input	[11:0]			bimm, //instrD[31], instrD[7], instrD[30:25], instrD[11:8], 12 bits
	input	[19:0]			uimm,
	input	[19:0]			jimm,
	input	[5:0]			EXTOp,
	output	reg [31:0] 	       immout);
   
always  @(*)
	 case (EXTOp)
		`EXT_CTRL_ITYPE_SHAMT:   immout<={27'b0,iimm_shamt[4:0]};
		`EXT_CTRL_ITYPE:	immout <= {{{20}{iimm[11]}}, iimm[11:0]};
		`EXT_CTRL_STYPE:	immout <= {{{20}{simm[11]}}, simm[11:0]};
		`EXT_CTRL_BTYPE:        immout <= {{{19}{bimm[11]}}, bimm[11:0], 1'b0};
		`EXT_CTRL_UTYPE:	immout <= {uimm[19:0], 12'b0}; //???????????12??0
		`EXT_CTRL_JTYPE:	immout <= {{{11}{jimm[19]}}, jimm[19:0], 1'b0};
		default:	        immout <= 32'b0;
	 endcase

       
endmodule

//从这里开始的都是新的，有pc的东西了

module NPC(PC, NPCOp, IMM, NPC,aluout, pcW);  // next pc module
    
   input  [31:0] PC;        // pc
   input  [2:0]  NPCOp;     // next pc operation
   input  [31:0] IMM;       // immediate
	input [31:0] aluout;
   
   output reg [31:0] NPC;   // next pc
   output [31:0] pcW;
   
   wire [31:0] PCPLUS4;
   
   assign PCPLUS4 = PC + 1; // pc + 4
   assign pcW = PC;
   
   always @(*) begin
      case (NPCOp)
          `NPC_PLUS4:  NPC = PCPLUS4;
          `NPC_BRANCH: NPC = PC+IMM;
          `NPC_JUMP:   NPC = PC+IMM;
		    `NPC_JALR:	  NPC = aluout;
          default:     NPC = PCPLUS4;
      endcase
   end 
   
endmodule

module PC( clk, rst, NPC, PC_out );

  input              clk;
  input              rst;
  input       [31:0] NPC;
  output reg  [31:0] PC_out;

  always @(posedge clk, posedge rst)
    if (rst) 
      PC <= 32'h0000_0000;
//      PC <= 32'h0000_3000;
    else
      PC <= NPC;
      
endmodule


`include "ctrl_encode_def.v"

module alu(A, B, ALUOp, C, Zero, PC);
           
   input  signed [31:0] A, B;
   input         [4:0]  ALUOp;
	input [31:0] PC;
   output signed [31:0] C;
   output Zero;
   
   reg [31:0] C;
   integer    i;
   //wire SB = B;
   wire [31:0] SB = $unsigned(B & 5'b11111);   // used to shifi operations
       
   always @( * ) begin
      case ( ALUOp )
      `ALUOp_nop:C=A;
      `ALUOp_lui:C=B;
      `ALUOp_auipc:C=PC+B;
      `ALUOp_add:C=A+B;
      `ALUOp_sub:C=A-B;
      `ALUOp_bne:C={31'b0,(A==B)};
      `ALUOp_blt:C={31'b0,(A>=B)};
      `ALUOp_bge:C={31'b0,(A<B)};
      `ALUOp_bltu:C={31'b0,($unsigned(A)>=$unsigned(B))};
      `ALUOp_bgeu:C={31'b0,($unsigned(A)<$unsigned(B))};
      `ALUOp_slt:C={31'b0,(A<B)};
      `ALUOp_sltu:C={31'b0,($unsigned(A)<$unsigned(B))};
      `ALUOp_xor:C=A^B;
      `ALUOp_or:C=A|B;
      `ALUOp_and:C=A&B;
      `ALUOp_sll:C=A<<SB;
      `ALUOp_srl:C=A>>SB;
      `ALUOp_sra:C=A>>>SB;
      `ALUOp_jalr: C = (A + B) & (~1);
      endcase
      // if (ALUOp == `ALUOp_sll) begin
      //    $display("alu sll result %d.", C);  //alu shift instructions debug
      // end
   end // end always
   
   assign Zero = (C == 32'b0);

endmodule
    