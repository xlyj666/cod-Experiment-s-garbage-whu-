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

`define GPRSel_RD 2'b00
`define GPRSel_RT 2'b01
`define GPRSel_31 2'b10

`define WDSel_FromALU 2'b00
`define WDSel_FromMEM 2'b01
`define WDSel_FromPC 2'b10

`define ALUOp_nop 5'b00000
`define ALUOp_lui 5'b00001
`define ALUOp_auipc 5'b00010
`define ALUOp_add 5'b00011
`define ALUOp_sub 5'b00100
`define ALUOp_bne 5'b00101
`define ALUOp_blt 5'b00110
`define ALUOp_bge 5'b00111
`define ALUOp_bltu 5'b01000
`define ALUOp_bgeu 5'b01001
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
		`EXT_CTRL_ITYPE:	immout <= {{{32-12}{iimm[11]}}, iimm[11:0]};
		`EXT_CTRL_STYPE:	immout <= {{{32-12}{simm[11]}}, simm[11:0]};
		`EXT_CTRL_BTYPE:        immout <= {{{32-13}{bimm[11]}}, bimm[11:0], 1'b0};
		`EXT_CTRL_UTYPE:	immout <= {uimm[19:0], 12'b0}; //???????????12??0
		`EXT_CTRL_JTYPE:	immout <= {{{32-21}{jimm[19]}}, jimm[19:0], 1'b0};
		default:	        immout <= 32'b0;
	 endcase

       
endmodule

module NPC(PC, NPCOp, IMM, NPC,aluout, pcW);  // next pc module
    
   input  [31:0] PC;        // pc
   input  [2:0]  NPCOp;     // next pc operation
   input  [31:0] IMM;       // immediate
	input [31:0] aluout;
   
   output reg [31:0] NPC;   // next pc
   output [31:0] pcW;
   
   wire [31:0] PCPLUS4;
   
   assign PCPLUS4 = PC + 4; // pc + 4
   assign pcW = PC;
   
   always @(*) begin
      case (NPCOp)
          `NPC_PLUS4:  NPC = PCPLUS4;
          `NPC_BRANCH: NPC = PC+IMM;
          `NPC_JUMP:   NPC = PC+IMM;
		    `NPC_JALR:	  NPC = aluout;
          default:     NPC = PCPLUS4;
      endcase
   end // end always
   
endmodule

module PC( clk, rst, NPC, PC );

  input              clk;
  input              rst;
  input       [31:0] NPC;
  output reg  [31:0] PC;

  always @(posedge clk, posedge rst)
    if (rst) 
      PC <= 32'h0000_0000;
//      PC <= 32'h0000_3000;
    else
      PC <= NPC;
      
endmodule

module RegFile (
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

// read logic
  always @(*) begin
      if (read_en_1) begin
        read_data_1 <= RegFile[read_addr_1];
        
        
      end //read data 1

      if (read_en_2) begin
        read_data_2 <= RegFile[read_addr_2];
        
        end
       //read data 2
  end

// write logic
  always @(posedge clk) begin

    if (rst) begin
      for (i=0; i<32; i=i+1) begin
        RegFile[i] <= 0;
      end // clear all registers when rst=1
      read_data_1 <= 0;
      read_data_2 <= 0;
    end //clear when rst=1

    else begin
      if (write_en) begin
        if ((read_addr_1 == write_addr)) begin //when read and write at the same register
            read_data_1 <= write_data;
            // if (write_addr != 0) begin
            // $display("x%d = %h", write_addr, write_data);
            // end
            end
        if ((read_addr_2 == write_addr)) begin //when read and write at the same register
            read_data_2 <= write_data;
            // if (write_addr != 0) begin
            // $display("x%d = %h", write_addr, write_data);
            // end
            end
        else begin
          RegFile[write_addr] <= write_data;
        end

        if (write_addr != 0) begin
            $display("x%d = %h", write_addr, write_data);
            // write print
            end
          RegFile[0] <= 0;  //cannot write to no.0 register.
      end //write data
      end
    end


endmodule


module riscv_SCPU(
    input      clk,            // clock
    input      reset,          // reset
    input [31:0]  inst_in,     // instruction
    input [31:0]  Data_in,     // data from data memory
   
    output    mem_w,          // output: memory write signal
    output [31:0] PC_out,     // PC address
      // memory write
    output [31:0] Addr_out,   // ALU output
    output [31:0] Data_out,// data to data memory

    output [31:0] pcW

    //input  [4:0] reg_sel,    // register selection (for debug use)
    //output [31:0] reg_data  // selected register data (for debug use)
    //output [2:0] DMType
);
    wire        RegWrite;    // control signal to register write
    wire [5:0]       EXTOp;       // control signal to signed extension
    wire [4:0]  ALUOp;       // ALU opertion
    wire [2:0]  NPCOp;       // next PC operation

    wire [1:0]  WDSel;       // (register) write data selection
    wire [1:0]  GPRSel;      // general purpose register selection
   
    wire        ALUSrc;      // ALU source for A
    wire        Zero;        // ALU ouput zero

    wire [31:0] NPC;         // next PC

    wire [4:0]  rs1;          // rs
    wire [4:0]  rs2;          // rt
    wire [4:0]  rd;          // rd
    wire [6:0]  Op;          // opcode
    wire [6:0]  Funct7;       // funct7
    wire [2:0]  Funct3;       // funct3
    wire [11:0] Imm12;       // 12-bit immediate
    wire [31:0] Imm32;       // 32-bit immediate
    wire [19:0] IMM;         // 20-bit immediate (address)
    wire [4:0]  A3;          // register address for write
    reg [31:0] WD;          // register write data
    wire [31:0] RD1,RD2;         // register data specified by rs
    wire [31:0] B;           // operator for ALU B
	
	wire [4:0] iimm_shamt;
	wire [11:0] iimm,simm,bimm;
	wire [19:0] uimm,jimm;
	wire [31:0] immout;
    wire[31:0] aluout;
    assign Addr_out=aluout;
	assign B = (ALUSrc) ? immout : RD2; // immout from EXT is immediate generated
	assign Data_out = RD2;
	
	assign iimm_shamt=inst_in[24:20];
	assign iimm=inst_in[31:20];
	assign simm={inst_in[31:25],inst_in[11:7]};
	assign bimm={inst_in[31],inst_in[7],inst_in[30:25],inst_in[11:8]};
	assign uimm=inst_in[31:12];
	assign jimm={inst_in[31],inst_in[19:12],inst_in[20],inst_in[30:21]};
   
    assign Op = inst_in[6:0];  // instruction
    assign Funct7 = inst_in[31:25]; // funct7
    assign Funct3 = inst_in[14:12]; // funct3
    assign rs1 = inst_in[19:15];  // rs1
    assign rs2 = inst_in[24:20];  // rs2
    assign rd = inst_in[11:7];  // rd
    assign Imm12 = inst_in[31:20];// 12-bit immediate
    assign IMM = inst_in[31:12];  // 20-bit immediate
   
   // instantiation of control unit
	     U_ctrl(
		.Op(Op), .Funct7(Funct7), .Funct3(Funct3), .Zero(Zero), 
		.RegWrite(RegWrite), .MemWrite(mem_w),
		.EXTOp(EXTOp), .ALUOp(ALUOp), .NPCOp(NPCOp), 
		.ALUSrc(ALUSrc), .DMType(DMType), .WDSel(WDSel)
	);
 // instantiation of pc unit
	PC U_PC(.clk(clk), .rst(reset), .NPC(NPC), .PC(PC_out) );
	NPC U_NPC(.PC(PC_out), .NPCOp(NPCOp), .IMM(immout), .NPC(NPC), .aluout(aluout), .pcW(pcW));
	EXT U_EXT(
		.iimm_shamt(iimm_shamt), .iimm(iimm), .simm(simm), .bimm(bimm),
		.uimm(uimm), .jimm(jimm),
		.EXTOp(EXTOp), .immout(immout)
	);
	RegFile U_RegFile(
		.clk(clk), .rst(reset),
		.write_en(RegWrite), 
		.read_addr_1(rs1), .read_addr_2(rs2), .write_addr(rd), 
		.write_data(WD), 
		.read_data_1(RD1), .read_data_2(RD2)
	);
    // instantiation of alu unit
	alu U_alu(.A(RD1), .B(B), .ALUOp(ALUOp), .C(aluout), .Zero(Zero), .PC(PC_out));

//please connnect the CPU by yourself
always @*
begin
	case(WDSel)
		`WDSel_FromALU: WD <= aluout;
		`WDSel_FromMEM: WD <= Data_in;
		`WDSel_FromPC:  WD <= PC_out+4;
	endcase
end


endmodule

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



module ctrl(Op, Funct7, Funct3, Zero, 
            RegWrite, MemWrite,
            EXTOp, ALUOp, NPCOp, 
            ALUSrc, GPRSel, WDSel,DMType
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
   output [1:0] GPRSel;   // general purpose register selection
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
	wire i_jalr = Op[6]&Op[5]&~Op[4]&~Op[3]&Op[2]&Op[1]&Op[0] & ~Funct3[2]& ~Funct3[1]& ~Funct3[0] ; //jalr 1100111 000

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


	assign ALUOp[0] = itype_l|stype|i_addi|i_ori|i_add|i_or|i_lui|i_slli|i_sll|i_sltu|i_sltiu;
	assign ALUOp[1] = i_jalr|itype_l|stype|i_addi|i_add|i_and|i_auipc|i_andi|i_slli|i_sll|i_sltu|i_slt|i_sltiu|i_slti|i_blt;
	assign ALUOp[2] = i_andi|i_and|i_ori|i_or|i_beq|i_sub|i_xori|i_xor|i_slli|i_sll|i_blt;
	assign ALUOp[3] = i_andi|i_and|i_ori|i_or|i_xori|i_xor|i_slli|i_sll|i_sltu|i_slt|i_sltiu|i_slti|i_bltu;
	assign ALUOp[4] = i_jalr;

endmodule


module imem(input  [31:0]   a,
            output [31:0]  rd);

  reg  [31:0] RAM[127:0];

  assign rd = RAM[a[8:2]]; // instruction size aligned
endmodule


module dmem(input                     clk, we,
            input  [31:0]        a, wd,
            input  [31:0]   pc,
            output [31:0]        rd);

  reg  [31:0] RAM[127:0];

  always @(negedge clk) begin
    if (we) begin
        RAM[a[8:2]] <= wd;          	  // sw
  	  end
    end
      
  assign rd = RAM[a[8:2]]; // word aligned (read word)

endmodule

//`include "xgriscv_defines.v"
module xgriscv_sc(clk, reset, pcW);//dm
  input             clk, reset;
  output [31:0]     pcW;
   
  wire [31:0]    instr;
  wire [31:0]    PC;
  wire           MemWrite;
  wire [31:0]    dm_addr, dm_din, dm_dout;

  //wire rstn;
  //assign rstn = ~reset;

  riscv_SCPU U_SCPU(
    .clk(clk),                 // input:  cpu clock
    .reset(reset),                 // input:  reset
    .inst_in(instr),             // input:  instruction
    .Data_in(dm_dout),        // input:  data to cpu  
    .mem_w(MemWrite),       // output: memory write signal
    .PC_out(PC),                   // output: PC
    .Addr_out(dm_addr),          // output: address from cpu to memory
    .Data_out(dm_din),        // output:    
    .pcW(pcW)
  );

  imem U_imem(
  .rd(instr),
  .a(PC)
  );

  dmem U_dmem(
    .clk(clk), 
    .we(MemWrite), 
    .a(dm_addr), 
    .wd(dm_din), 
    .rd(dm_d
    
    out), 
    .pc(PC)
    );
  
endmodule