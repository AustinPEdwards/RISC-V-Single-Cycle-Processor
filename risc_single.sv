// AUSTIN EDWARDS CSCE 342 ASSIGNMENT 6
// RISC-V single-cycle processor
// Based on Section 7.6 of Digital Design & Computer Architecture

module testbench();

  logic        clk, reset;

  logic [31:0] DataAdr, WriteData, PC;

  riscvsingle dut(  .clk(clk),
                    .reset(reset), 
                    .PC(PC), 
                    .ALUResult(DataAdr), 
                    .WriteData(WriteData));  
  
  // initialize test
  initial
    begin
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(PC===32'h00_00_00_14) begin
        if(DataAdr === 88 & WriteData === 32'hBEEEF009) begin
          $display("Simulation succeeded");
          $stop;
        end else begin
          $display("Simulation failed");
          $stop;
        end
      end
    end
endmodule

module riscvsingle(input  logic        clk, reset,
                   output logic [31:0] ALUResult, WriteData, PC);

  logic         ALUSrc, RegWrite, Jump, Zero, MemWrite;
  logic [1:0]   ResultSrc;
  logic [2:0]   ImmSrc; // CHANGED THIS TO A 3 BIT BUS
  logic [2:0]   ALUControl;
  logic [31:0]  Instr;

  controller c(     .op(Instr[6:0]),
                    .funct3(Instr[14:12]), 
                    .funct7b5(Instr[30]), 
                    .Zero(Zero),
                    .ResultSrc(ResultSrc), 
                    .MemWrite(MemWrite), 
                    .PCSrc(PCSrc),
                    .ALUSrc(ALUSrc),
                    .RegWrite(RegWrite),
                    .Jump(Jump),
                    .ImmSrc(ImmSrc),
                    .ALUControl(ALUControl));              
               
  datapath dp(      .clk(clk), 
                    .reset(reset), 
                    .ResultSrc(ResultSrc),
                    .PCSrc(PCSrc),
                    .ALUSrc(ALUSrc), 
                    .RegWrite(RegWrite),
                    .ImmSrc(ImmSrc), 
                    .ALUControl(ALUControl),
                    .MemWrite(MemWrite),
                    .Zero(Zero),
                    .ALUResult(ALUResult), 
                    .WriteData(WriteData), 
                    .Instr(Instr),
                    .PC(PC));
endmodule

module datapath(input  logic        clk, reset,PCSrc, ALUSrc, RegWrite, MemWrite,
                input  logic [1:0]  ResultSrc, 
                input  logic [2:0]  ImmSrc,
                input  logic [2:0]  ALUControl,
                output logic        Zero,
                output logic [31:0] ALUResult, WriteData, Instr, PC);

  logic [31:0]  PCNext, PCPlus4, PCTarget;
  logic [31:0]  ImmExt, SrcA, SrcB, Result, ReadData;

  always_ff @ ( posedge clk )
    if( reset ) PC  <=  32'b0;
    else        PC  <=  PCNext;

  assign PCPlus4 = PC + 32'd4;

  assign PCTarget = PC + ImmExt;
  
  assign PCNext = PCSrc ? PCTarget : PCPlus4;
 
  imem      imem(   .a(PC), 
                    .rd(Instr));
   
  regfile   rf(     .clk(clk),
                    .we3(RegWrite), 
                    .a1(Instr[19:15]),
                    .a2(Instr[24:20]), 
                    .a3(Instr[11:7]),
                    .wd3(Result),
                    .rd1(SrcA),
                    .rd2(WriteData) );
                            
  extend    ext(    .instr(Instr[31:7]), 
                    .immsrc(ImmSrc),
                    .immext(ImmExt) );

  assign    SrcB = ALUSrc ? ImmExt : WriteData;
  
  // WHEN THE OP CODE IS A LUI INSTRUCTION:
  // SET THE IMMEDIATE EXTENDER TO THE UPPER FORMAT (20 BIT IMMEDIATE + 12'b0)
  // ALSO SET SrcB to ZERO, COULDN't FIND A WORK AROUND, ADDING SrcA AND SrcB in ALU
  assign    SrcA = (Instr[6:0] == 7'b0110111) ? ImmExt : SrcA;
  assign    SrcB = (Instr[6:0] == 7'b0110111) ? 32'b0 : SrcB;

    
  alu       alu(    .a(SrcA), 
                    .b(SrcB), 
                    .alucontrol(ALUControl), 
                    .result(ALUResult),
                    .zero(Zero));

  dmem      dmem(   .clk(clk), 
                    .we(MemWrite), 
                    .a(ALUResult), 
                    .wd(WriteData), 
                    .rd(ReadData) );

  always_comb
	case( ResultSrc )
		2'b00:		Result = ALUResult;
		2'b01:		Result = ReadData;
		2'b10:		Result = PCPlus4;
		default:	Result = 2'bxx;
	endcase
  
endmodule

module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [ 4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [2:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
      3'b000:   immext = {{20{instr[31]}}, instr[31:20]};  // I-Type
      3'b001:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};  // S-Type
      3'b010:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};  // B-Type
      3'b011:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};  // J-Type
      3'b100:   immext = {{20{instr[31:12]}}, 12'b0};  // U-Type
      default:  immext = 32'bx;
    endcase             
endmodule

module imem(input  logic [31:0] a,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  initial
      $readmemh("Program_2.dat",RAM);

  assign rd = RAM[a[31:2]];
endmodule

module dmem(input  logic        clk, we,
            input  logic [31:0] a, wd,
            output logic [31:0] rd);

  logic [31:0] RAM[63:0];

  assign rd = RAM[a[31:2]];

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule

module alu( input  logic [2:0]  alucontrol,
            input  logic [31:0] a, b,
            output logic [31:0] result,
            output logic        zero);

  logic [31:0] condinvb, sum;
  logic        v; 
  logic        isAddSub;

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];
  assign isAddSub = (~alucontrol[2] & ~alucontrol[1]) | (~alucontrol[1] & alucontrol[0]);

  always_comb
    case (alucontrol)
      3'b000:  result = sum;		// add
      3'b001:  result = sum;		// subtract
      3'b010:  result = a & b;		// and
      3'b011:  result = a | b;		// or
      3'b100:  result = a ^ b;		// xor
      3'b101:  result = sum[31] ^ v;	// slt
      3'b110:  result = a << b[4:0];	// sll
      3'b111:  result = a >> b[4:0];	// srl
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
  assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
  
endmodule


module controller(  input  logic       funct7b5, Zero,
                    input  logic [2:0] funct3,
                    input  logic [6:0] op,
                    output logic       MemWrite, PCSrc, ALUSrc, RegWrite, Jump,
                    output logic [2:0] ImmSrc,
                    output logic [1:0] ResultSrc,
                    output logic [2:0] ALUControl
                    );

  logic       Branch;
  logic [1:0] ALUOp;
  logic [11:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite, ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
      7'b0000011: controls = 12'b1_000_1_0_01_0_00_0;	// lw
      7'b0100011: controls = 12'b0_001_1_1_00_0_00_0;	// sw	
      7'b0110011: controls = 12'b1_xxx_0_0_00_0_10_0;	// R-type
      7'b1100011: controls = 12'b0_010_0_0_00_1_01_0;	// beq
      7'b0010011: controls = 12'b1_000_1_0_00_0_10_0;	// I-type
      7'b1101111: controls = 12'b1_011_0_0_10_0_00_1;	// jal
      7'b0110111: controls = 12'b1_100_1_0_00_0_00_0;	// U-type
      default:    controls = 12'bx_xxx_x_x_xx_x_xx_x;
    endcase
  
  
  logic  RtypeSub;
  assign RtypeSub = funct7b5 & op[5]; 

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000;  // addition
      2'b01:                ALUControl = 3'b001;  // subtraction
      default: case(funct3)			  // R or I-type
                 3'b000:  if (RtypeSub) 	  
                            ALUControl = 3'b001;  // sub
                          else          
                            ALUControl = 3'b000;  // add, addi
                 3'b010:    ALUControl = 3'b101;  // slt, slti
                 3'b110:    ALUControl = 3'b011;  // or, ori
                 3'b111:    ALUControl = 3'b010;  // and, andi
                 3'b100:    ALUControl = 3'b100;  // xor
                 default:   ALUControl = 3'bxxx;
               endcase
    endcase

  assign PCSrc = Branch & Zero | Jump;
endmodule