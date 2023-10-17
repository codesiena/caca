module mycpu_top(
    input  wire        clk,
    input  wire        resetn,
    // inst sram interface
    output wire        inst_sram_en,
    output wire [ 3:0] inst_sram_we,
    output wire [31:0] inst_sram_addr,
    output wire [31:0] inst_sram_wdata,
    input  wire [31:0] inst_sram_rdata,
    // data sram interface
    output wire        data_sram_en,
    output wire [ 3:0] data_sram_we,
    output wire [31:0] data_sram_addr,
    output wire [31:0] data_sram_wdata,
    input  wire [31:0] data_sram_rdata,
    // trace debug interface
    output wire [31:0] debug_wb_pc,
    output wire [ 3:0] debug_wb_rf_we,
    output wire [ 4:0] debug_wb_rf_wnum,
    output wire [31:0] debug_wb_rf_wdata
);
reg         reset;
    always @(posedge clk) reset <= ~resetn;
wire        if_allow;
wire        id_allow;
wire        exe_allow;
wire        mem_allow;
wire        wb_allow;

wire        if_to_id_valid;
wire        id_to_exe_valid;
wire        exe_to_mem_valid;
wire        mem_to_wb_valid;//握手信号

reg         [31:0] if_pc;
reg         [31:0] id_pc;
reg         [31:0] exe_pc;
reg         [31:0] mem_pc;//PC在不同流水阶段的截断值
reg         [31:0] wb_pc;
    
reg         if_valid;
reg         id_valid;
reg         exe_valid;
reg         mem_valid;
reg         wb_valid;
    
wire        if_ready_go;
wire        id_ready_go;
wire        exe_ready_go;
wire        mem_ready_go;
wire        wb_ready_go;
wire [31:0] seq_pc;
wire [31:0] nextpc;
wire        br_taken;
wire [31:0] br_target;

wire [11:0] alu_op;
wire        load_op;
wire        src1_is_pc;
wire        src2_is_imm;
wire        res_from_mem;
wire        dst_is_r1;
wire        gr_we;
wire        mem_we;
wire        src_reg_is_rd;
wire [4: 0] dest;
wire [31:0] rj_value;
wire [31:0] rkd_value;
wire [31:0] imm;
wire [31:0] br_offs;
wire [31:0] jirl_offs;

wire [ 5:0] op_31_26;
wire [ 3:0] op_25_22;
wire [ 1:0] op_21_20;
wire [ 4:0] op_19_15;
wire [ 4:0] rd;
wire [ 4:0] rj;
wire [ 4:0] rk;
wire [11:0] i12;
wire [19:0] i20;
wire [15:0] i16;
wire [25:0] i26;

wire [63:0] op_31_26_d;
wire [15:0] op_25_22_d;
wire [ 3:0] op_21_20_d;
wire [31:0] op_19_15_d;

wire        inst_add_w;
wire        inst_sub_w;
wire        inst_slt;
wire        inst_sltu;
wire        inst_nor;
wire        inst_and;
wire        inst_or;
wire        inst_xor;
wire        inst_slli_w;
wire        inst_srli_w;
wire        inst_srai_w;
wire        inst_addi_w;
wire        inst_ld_w;
wire        inst_st_w;
wire        inst_jirl;
wire        inst_b;
wire        inst_bl;
wire        inst_beq;
wire        inst_bne;
wire        inst_lu12i_w;
wire        inst_slti;
wire        inst_sltui;
wire        inst_andi;
wire        inst_ori;
wire        inst_xori;
wire        inst_sll_w;
wire        inst_srl_w;
wire        inst_sra_w;
wire        inst_pcaddu12i;
wire        inst_mul_w;
wire        inst_mulh_w;
wire        inst_mulh_wu;
wire        inst_div_w;
wire        inst_mod_w;
wire        inst_div_wu;
wire        inst_mod_wu;

wire        need_ui5;
wire        need_si12;
wire        need_ui12;
wire        need_si16;
wire        need_si20;
wire        need_si26;
wire        src2_is_4;

wire [ 4:0] rf_raddr1;
wire [31:0] rf_rdata1;
wire [ 4:0] rf_raddr2;
wire [31:0] rf_rdata2;
wire        rf_we   ;
wire [ 4:0] rf_waddr;
wire [31:0] rf_wdata;

wire [31:0] alu_src1   ;
wire [31:0] alu_src2   ;
wire [31:0] exe_alu_result ;
//wire [31:0] final_result;
wire [31:0] mem_result;

wire        read_after_wr_ld;
wire [31:0] fur_rj_value;
wire [31:0] fur_rk_value;
wire [31:0] fur_rd_value;

reg [31:0] mem_rkd_value;

reg [31:0]inst; 

reg [31:0]mem_alu_result;

reg  [ 4:0] exe_rf_waddr;
reg         exe_rf_we;

wire [31:0] mem_rf_wdata;
reg  [ 4:0] mem_rf_waddr;
reg         mem_rf_we;

reg  [31:0] wb_rf_wdata;
reg  [ 4:0] wb_rf_waddr;
reg         wb_rf_we;

reg exe_res_from_mem;
reg mem_res_from_mem;
//////////////////////////////////////////////////////////// * IF * ////////////////////////////////////////////////////////////

assign if_ready_go      = 1'b1;                                     //IF级握手信号
assign if_allow         = ~if_valid | if_ready_go & id_allow;     

always @(posedge clk) begin                                         //IF级valid信号，复位信号结束后恒为1
    if_valid <= resetn; // 在reset撤销的下一个时钟上升沿才开始取指
end
           
assign seq_pc       = (if_allow)? if_pc + 3'h4 : if_pc;             //ID级阻塞时，nextpc不更新
assign nextpc       = (br_taken & if_allow) ? br_target : seq_pc;

always @(posedge clk) begin
    if (~resetn) begin
        if_pc <= 32'h1bfffffc;     //trick: to make nextpc be 0x1c000000 during reset 
    end
    else begin
        if_pc <= nextpc;
    end
end

assign inst_sram_en    = if_allow & resetn;                         //指令RAM相关信号
assign inst_sram_we    = 4'b0;                                              
assign inst_sram_addr  = nextpc;//pre_if                                    
assign inst_sram_wdata = 32'b0;  

//////////////////////////////////////////////////////////// * ID * ////////////////////////////////////////////////////////////
                                      
assign id_ready_go      = ~read_after_wr_ld;                        //ID级握手信号
assign id_allow         =  ~id_valid | id_ready_go & exe_allow;     
assign if_to_id_valid   = if_valid  & if_ready_go;                 

always @(posedge clk) begin                                         //ID级valid信号
    if(~resetn)
        id_valid <= 1'b0;  
    else if(id_allow)
        // 有效条件：if向id输入有效、非转移指令、id允许接收数据
        id_valid <= if_to_id_valid &~br_taken;
end

always @(posedge clk) begin        //PC
    if(~resetn) 
        id_pc <= 1'b0;
    if(if_to_id_valid & id_allow) begin
        id_pc <= if_pc;
    end
end

always @(posedge clk) begin        //ID级指令，用于译码
    if(~resetn) 
        inst <= 32'b0;     
    if(if_to_id_valid & id_allow) begin
        inst  <= inst_sram_rdata;
    end
end

assign op_31_26  = inst[31:26];
assign op_25_22  = inst[25:22];
assign op_21_20  = inst[21:20];
assign op_19_15  = inst[19:15];

assign rd   = inst[ 4: 0];
assign rj   = inst[ 9: 5];
assign rk   = inst[14:10];

assign i12  = inst[21:10];
assign i20  = inst[24: 5];
assign i16  = inst[25:10];
assign i26  = {inst[ 9: 0], inst[25:10]};

decoder_6_64 u_dec0(.in(op_31_26 ), .out(op_31_26_d ));
decoder_4_16 u_dec1(.in(op_25_22 ), .out(op_25_22_d ));
decoder_2_4  u_dec2(.in(op_21_20 ), .out(op_21_20_d ));
decoder_5_32 u_dec3(.in(op_19_15 ), .out(op_19_15_d ));

assign inst_add_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h00];
assign inst_sub_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h02];
assign inst_slt      = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h04];
assign inst_sltu     = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h05];
assign inst_nor      = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h08];
assign inst_and      = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h09];
assign inst_or       = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0a];
assign inst_xor      = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0b];
assign inst_slli_w   = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h01];
assign inst_srli_w   = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h09];
assign inst_srai_w   = op_31_26_d[6'h00] & op_25_22_d[4'h1] & op_21_20_d[2'h0] & op_19_15_d[5'h11];
assign inst_addi_w   = op_31_26_d[6'h00] & op_25_22_d[4'ha];
assign inst_ld_w     = op_31_26_d[6'h0a] & op_25_22_d[4'h2];
assign inst_st_w     = op_31_26_d[6'h0a] & op_25_22_d[4'h6];
assign inst_jirl     = op_31_26_d[6'h13];
assign inst_b        = op_31_26_d[6'h14];
assign inst_bl       = op_31_26_d[6'h15];
assign inst_beq      = op_31_26_d[6'h16];
assign inst_bne      = op_31_26_d[6'h17];
assign inst_lu12i_w  = op_31_26_d[6'h05] & ~inst[25];
assign inst_slti     = op_31_26_d[6'h00] & op_25_22_d[4'h8];
assign inst_sltui    = op_31_26_d[6'h00] & op_25_22_d[4'h9];
assign inst_andi     = op_31_26_d[6'h00] & op_25_22_d[4'hd];
assign inst_ori      = op_31_26_d[6'h00] & op_25_22_d[4'he]; 
assign inst_xori     = op_31_26_d[6'h00] & op_25_22_d[4'hf];
assign inst_sll_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0e];
assign inst_srl_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h0f];
assign inst_sra_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h10];
assign inst_pcaddu12i= op_31_26_d[6'h07] & ~inst[25];
assign inst_mul_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h18];
assign inst_mulh_w   = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h19];
assign inst_mulh_wu  = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h1] & op_19_15_d[5'h1a];
assign inst_div_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h2] & op_19_15_d[5'h00];
assign inst_mod_w    = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h2] & op_19_15_d[5'h01];
assign inst_div_wu   = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h2] & op_19_15_d[5'h02];
assign inst_mod_wu   = op_31_26_d[6'h00] & op_25_22_d[4'h0] & op_21_20_d[2'h2] & op_19_15_d[5'h03];

assign alu_op[ 0] = inst_add_w | inst_addi_w | inst_ld_w | inst_st_w | 
                    inst_jirl  | inst_bl | inst_pcaddu12i;//新增pcaddu12i
assign alu_op[ 1] = inst_sub_w;
assign alu_op[ 2] = inst_slt  | inst_slti;
assign alu_op[ 3] = inst_sltu | inst_sltui;
assign alu_op[ 4] = inst_and  | inst_andi;
assign alu_op[ 5] = inst_nor;
assign alu_op[ 6] = inst_or   | inst_ori;
assign alu_op[ 7] = inst_xor  | inst_xori;
assign alu_op[ 8] = inst_slli_w | inst_sll_w;
assign alu_op[ 9] = inst_srli_w | inst_srl_w;
assign alu_op[10] = inst_srai_w | inst_sra_w;
assign alu_op[11] = inst_lu12i_w;

assign alu_src1 = src1_is_pc  ? id_pc[31:0] : rj_value;
assign alu_src2 = src2_is_imm ? imm : rkd_value;  

assign need_ui5   =  inst_slli_w | inst_srli_w | inst_srai_w;
assign need_si12  =  inst_addi_w | inst_ld_w | inst_st_w | inst_slti | inst_sltui;
assign need_ui12  =  inst_andi | inst_ori  | inst_xori;
assign need_si16  =  inst_jirl | inst_beq | inst_bne;
assign need_si20  =  inst_lu12i_w | inst_pcaddu12i;
assign need_si26  =  inst_b | inst_bl;
assign src2_is_4  =  inst_jirl | inst_bl;

assign imm = src2_is_4 ? 32'h4                      :
             need_si20 ? {i20[19:0], 12'b0}         :
             need_ui12 ? {20'b0, i12[11:0]}         :
/*need_ui5 || need_si12*/{{20{i12[11]}}, i12[11:0]} ;

assign br_offs = need_si26 ? {{ 4{i26[25]}}, i26[25:0], 2'b0} :
                             {{14{i16[15]}}, i16[15:0], 2'b0} ;

assign jirl_offs = {{14{i16[15]}}, i16[15:0], 2'b0};

assign src_reg_is_rd = inst_beq | inst_bne | inst_st_w;

assign src1_is_pc    = inst_jirl | inst_bl | inst_pcaddu12i;

assign src2_is_imm   = inst_slli_w | inst_srli_w | inst_srai_w | inst_addi_w | inst_ld_w   |
                       inst_st_w   | inst_lu12i_w| inst_jirl   | inst_bl     | inst_slti   |
                       inst_sltui  | inst_andi   | inst_ori    | inst_xori   | inst_pcaddu12i;

assign rf_raddr1 = rj;
assign rf_raddr2 = src_reg_is_rd ? rd :rk;

regfile u_regfile(
    .clk    (clk      ),
    .raddr1 (rf_raddr1),
    .rdata1 (rf_rdata1),
    .raddr2 (rf_raddr2),
    .rdata2 (rf_rdata2),
    .we     (rf_we    ),
    .waddr  (rf_waddr ),
    .wdata  (rf_wdata )
    );

assign res_from_mem  = inst_ld_w;
assign dst_is_r1     = inst_bl;
assign gr_we         = ~inst_st_w & ~inst_beq & ~inst_bne & ~inst_b;
assign mem_we        = inst_st_w;
assign dest          = dst_is_r1 ? 5'd1 : rd;
assign rj_eq_rd      = (rj_value == rkd_value);
    
wire rj_read;           //指令需要读rj
wire rk_read;           //指令需要读rk
wire rd_read;           //指令需要读rd

assign rj_read = inst_add_w  | inst_sub_w  | inst_slt    | inst_sltu   | 
                 inst_slli_w | inst_srli_w | inst_srai_w | inst_addi_w |
                 inst_or     | inst_nor    | inst_xor    | inst_and    |
                 inst_bne    | inst_beq    | inst_st_w   | inst_ld_w   |
                 inst_slti   | inst_sltui  | inst_andi   | inst_ori    |
                 inst_xori   | inst_sll_w  | inst_srl_w  | inst_sra_w  |
                 inst_mul_w  | inst_mulh_w | inst_mulh_wu| inst_jirl   |
                 inst_div_w  | inst_mod_w  | inst_div_wu | inst_mod_wu ;
    
assign rk_read = inst_add_w  | inst_sub_w  | inst_slt    | inst_sltu   |
                 inst_or     | inst_nor    | inst_xor    | inst_and    |
                 inst_sll_w  | inst_srl_w  | inst_sra_w  | inst_mul_w  |
                 inst_mulh_w | inst_mulh_wu| inst_div_w  | inst_mod_w  |
                 inst_div_wu | inst_mod_wu ;

assign rd_read = inst_bne    | inst_beq    | inst_st_w;

wire read_after_wr ;        //写后读存在信号
wire read_after_wr_rj;      //读rj寄存器的指令产生写后读
wire read_after_wr_rk;      //读rk寄存器的指令产生写后读
wire raed_after_wr_rd;      //读rd寄存器的指令产生写后读

assign read_after_wr_rj =  rj_read & (rj!=5'b0) & ( (rj == exe_rf_waddr) & exe_rf_we |
                                                    (rj == mem_rf_waddr) & mem_rf_we |
                                                    (rj == wb_rf_waddr ) & wb_rf_we  );
                                                    
assign read_after_wr_rk =  rk_read & (rk!=5'b0) & ( (rk == exe_rf_waddr) & exe_rf_we |
                                                    (rk == mem_rf_waddr) & mem_rf_we |
                                                    (rk == wb_rf_waddr ) & wb_rf_we  ); 
                                                                            
assign raed_after_wr_rd =  rd_read & (rd!=5'b0) & ( (rd == exe_rf_waddr) & exe_rf_we |
                                                    (rd == mem_rf_waddr) & mem_rf_we |
                                                    (rd == wb_rf_waddr ) & wb_rf_we );
                                                        
assign read_after_wr =   read_after_wr_rj | read_after_wr_rk | raed_after_wr_rd;

assign read_after_wr_ld = exe_res_from_mem     &            //前递时由于ld指令，需要一拍延迟，之后随着指令增加应该要修改
                         (rj_read & (rj!=5'b0) & (rj == exe_rf_waddr) & exe_rf_we |
                          rk_read & (rk!=5'b0) & (rk == exe_rf_waddr) & exe_rf_we |
                          rd_read & (rk!=5'b0) & (rd == exe_rf_waddr) & exe_rf_we ); 

assign fur_rj_value = (rj == exe_rf_waddr) & exe_rf_we ? exe_alu_result :           //rj前递数据
                      (rj == mem_rf_waddr) & mem_rf_we ? mem_rf_wdata   :
                      (rj == wb_rf_waddr ) & wb_rf_we  ? wb_rf_wdata    : 32'b0;
 
assign fur_rk_value = (rk == exe_rf_waddr) & exe_rf_we ? exe_alu_result :           //rk前递数据
                      (rk == mem_rf_waddr) & mem_rf_we ? mem_rf_wdata   :
                      (rk == wb_rf_waddr ) & wb_rf_we  ? wb_rf_wdata    : 32'b0;
                        
assign fur_rd_value = (rd == exe_rf_waddr) & exe_rf_we ? exe_alu_result :           //rd前递数据      
                      (rd == mem_rf_waddr) & mem_rf_we ? mem_rf_wdata   :
                      (rd == wb_rf_waddr ) & wb_rf_we  ? wb_rf_wdata    : 32'b0;

assign rj_value      = read_after_wr_rj ? fur_rj_value : rf_rdata1;
assign rkd_value     = read_after_wr_rk ? fur_rk_value :
                       raed_after_wr_rd ? fur_rd_value : rf_rdata2;

wire id_rf_we;
wire [4:0]id_rf_waddr;
assign id_rf_we    = gr_we; 
assign id_rf_waddr = dest;      

assign br_taken = (   inst_beq  &&  rj_eq_rd
                   || inst_bne  && !rj_eq_rd
                   || inst_jirl
                   || inst_bl
                   || inst_b
                  ) && id_valid;
assign br_target = (inst_beq || inst_bne || inst_bl || inst_b) ? (id_pc + br_offs) :
                                                   /*inst_jirl*/ (rj_value + jirl_offs);
                                                   
//ID级乘法指令相关 
wire res_from_mul    = inst_mul_w | inst_mulh_w | inst_mulh_wu;
wire [32:0] mul_src1 = inst_mulh_wu ? {1'b0, rj_value } : {rj_value[31] , rj_value};
wire [32:0] mul_src2 = inst_mulh_wu ? {1'b0, rkd_value} : {rkd_value[31], rkd_value};

//ID级除法指令相关
wire [31:0] div_src1 = rj_value;
wire [31:0] div_src2 = rkd_value; 

wire is_div = inst_div_w | inst_mod_w | inst_div_wu | inst_mod_wu; 
                      
//////////////////////////////////////////////////////////// * EXE * ////////////////////////////////////////////////////////////

reg exe_is_div;
reg exe_inst_div_w;
reg exe_inst_mod_w;
reg exe_inst_div_wu;
reg exe_inst_mod_wu;

assign exe_ready_go      = ~exe_is_div |                                        //EXE级握手信号
                           dout_tvalid_s & (exe_inst_div_w | exe_inst_mod_w )|
                           dout_tvalid_u & (exe_inst_div_wu| exe_inst_mod_wu);                    
assign exe_allow         = ~exe_valid | exe_ready_go & mem_allow; 
assign id_to_exe_valid  = id_valid & id_ready_go;    

always @(posedge clk) begin                         //EXE级valid信号
    if(~resetn)
        exe_valid <= 1'b0;
    else if(exe_allow)
        exe_valid <= id_to_exe_valid; 
end

always@(posedge clk)begin           //PC
    if(~resetn) 
        exe_pc <= 1'b0;
    if(id_to_exe_valid & exe_allow) begin
        exe_pc <=id_pc;
    end
end

always @ (posedge clk)begin          //寄存器写数据选择信号
    if(~resetn)
        exe_res_from_mem <= 1'b0;
    if(id_to_exe_valid & exe_allow) 
        exe_res_from_mem <= res_from_mem;
end

reg exe_mem_we;                     //数据RAM写使能与写数据
reg [31:0] exe_rkd_value;
always @ (posedge clk)begin
    if(~resetn)
        exe_mem_we <= 1'b0;
        exe_rkd_value <= 32'b0;
    if(id_to_exe_valid & exe_allow)  
        exe_rkd_value <= rkd_value;
        exe_mem_we <= mem_we;
end

always @ (posedge clk)begin         //寄存器写地址与使能信号
    if(~resetn)
        {exe_rf_we,exe_rf_waddr}<=6'b0;                
    if(id_to_exe_valid & exe_allow) 
        {exe_rf_we,exe_rf_waddr} <= {id_rf_we,id_rf_waddr};
    else if(exe_to_mem_valid & mem_allow)
        {exe_rf_we,exe_rf_waddr} <= 6'b0;
end

reg [31:0] exe_alu_src1;            //alu操作数与op信号
reg [31:0] exe_alu_src2;
reg [11:0] exe_alu_op;
always @ (posedge clk)begin
   if(~resetn)
        exe_alu_src1 <=32'b0;
        exe_alu_src2 <=32'b0;
        exe_alu_op <= 12'b0;
    if(id_to_exe_valid & exe_allow) begin
        exe_alu_src1 <=alu_src1;
        exe_alu_src2 <=alu_src2;
        exe_alu_op <=alu_op;
    end
end

alu u_alu(                          //alu接线
    .alu_op     (exe_alu_op    ),
    .alu_src1   (exe_alu_src1  ),
    .alu_src2   (exe_alu_src2  ),
    .alu_result (exe_alu_result)
    );

/* ---------- 乘法相关 ------------ */
reg [32:0] exe_mul_src1;                               
reg [32:0] exe_mul_src2;
reg exe_res_from_mul;
always @ (posedge clk)begin
    if(~resetn)
        exe_mul_src1 <= 33'b0;
        exe_mul_src2 <= 33'b0;
        exe_res_from_mul <= 1'b0;
    if(id_to_exe_valid & exe_allow)  
        exe_mul_src1 <= mul_src1;
        exe_mul_src2 <= mul_src2;
        exe_res_from_mul <= res_from_mul;
end

reg exe_inst_mul_w;     //决定取低位还是高位
always @ (posedge clk)begin
    if(~resetn)
        exe_inst_mul_w <= 1'b0;
    if(id_to_exe_valid & exe_allow)  
        exe_inst_mul_w <= inst_mul_w;
end

wire [65:0] signed_prod;
wire [31:0] exe_mul_result;
assign signed_prod = $signed(exe_mul_src1) * $signed(exe_mul_src2);
assign exe_mul_result  = exe_inst_mul_w ? signed_prod[31:0] : signed_prod[63:32];

/* ---------- 除法相关 ------------ */                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

    reg [31:0] exe_div_src1;                               
    reg [31:0] exe_div_src2;
    always @ (posedge clk)begin
        if(~resetn) begin
            exe_div_src1 <= 32'b0;
            exe_div_src2 <= 32'b0;
        end
        else if(id_to_exe_valid & exe_allow) begin  
            exe_div_src1 <= div_src1;
            exe_div_src2 <= div_src2;
        end
        else begin
        end
    end

    always @ (posedge clk)begin
        if(~resetn) begin
            exe_is_div <= 1'b0;
            exe_inst_div_w <= 1'b0;
            exe_inst_mod_w <= 1'b0;
            exe_inst_div_wu <= 1'b0;
            exe_inst_mod_wu <= 1'b0;
        end
        else if(id_to_exe_valid & exe_allow) begin
            exe_is_div <= is_div;
            exe_inst_div_w <= inst_div_w;
            exe_inst_mod_w <= inst_mod_w;
            exe_inst_div_wu <= inst_div_wu;
            exe_inst_mod_wu <= inst_mod_wu;
        end
    end

    reg exe_divisor_tvalid_s;//除数输入通道握手信号valid
    always @ (posedge clk)begin
        if(~resetn) begin
            exe_divisor_tvalid_s <= 1'b0;
        end
        else if(id_to_exe_valid & exe_allow & (inst_div_w | inst_mod_w)) begin  
            exe_divisor_tvalid_s <= 1'b1;
        end 
        else if(divisor_tready_s) begin//握手成功
            exe_divisor_tvalid_s <= 1'b0;
        end
    end

    reg exe_dividend_tvalid_s;
    always @ (posedge clk)begin
        if(~resetn) begin
            exe_dividend_tvalid_s <= 1'b0;
        end
        else if(id_to_exe_valid & exe_allow & (inst_div_w | inst_mod_w)) begin  
            exe_dividend_tvalid_s <= 1'b1;
        end
        else if(dividend_tready_s) begin
            exe_dividend_tvalid_s <= 1'b0;
        end
    end

    wire [31:0] dividend_tdata_s;
    wire [31:0] divisor_tdata_s;
    assign dividend_tdata_s  = exe_div_src1;
    assign divisor_tdata_s   = exe_div_src2;
    assign divisor_tvalid_s  = exe_divisor_tvalid_s;
    assign dividend_tvalid_s = exe_dividend_tvalid_s;

    wire [63:0] dout_tdata_s;
    mydiv_signed div_s (        //调用有符号除法器
    .aclk(clk),                                       // input wire aclk
    .s_axis_divisor_tvalid(divisor_tvalid_s),         // input wire s_axis_divisor_tvalid
    .s_axis_divisor_tready(divisor_tready_s),         // output wire s_axis_divisor_tready            
    .s_axis_divisor_tdata(divisor_tdata_s),           // input wire [31 : 0] s_axis_divisor_tdata     除数
    .s_axis_dividend_tvalid(dividend_tvalid_s),       // input wire s_axis_dividend_tvalid
    .s_axis_dividend_tready(dividend_tready_s),       // output wire s_axis_dividend_tready           
    .s_axis_dividend_tdata(dividend_tdata_s),         // input wire [31 : 0] s_axis_dividend_tdata    被除数
    .m_axis_dout_tvalid(dout_tvalid_s),               // output wire m_axis_dout_tvalid
    .m_axis_dout_tdata(dout_tdata_s)                  // output wire [63 : 0] m_axis_dout_tdata
    );

    reg exe_divisor_tvalid_u;
    always @ (posedge clk)begin
        if(~resetn) begin
            exe_divisor_tvalid_u <= 1'b0;
        end
        else if(id_to_exe_valid & exe_allow & (inst_div_wu | inst_mod_wu)) begin  
            exe_divisor_tvalid_u <= 1'b1;
        end
        else if(divisor_tready_u) begin
            exe_divisor_tvalid_u <= 1'b0;
        end
    end

    reg exe_dividend_tvalid_u;
    always @ (posedge clk)begin
        if(~resetn) begin
            exe_dividend_tvalid_u <= 1'b0;
        end
        else if(id_to_exe_valid & exe_allow & (inst_div_wu | inst_mod_wu)) begin  
            exe_dividend_tvalid_u <= 1'b1;
        end
        else if(dividend_tready_u) begin
            exe_dividend_tvalid_u <= 1'b0;
        end
    end

    wire [31:0] dividend_tdata_u;
    wire [31:0] divisor_tdata_u;
    assign dividend_tdata_u = exe_div_src1;
    assign divisor_tdata_u  = exe_div_src2;
    assign divisor_tvalid_u = exe_divisor_tvalid_u;
    assign dividend_tvalid_u = exe_dividend_tvalid_u;

    wire [63:0] dout_tdata_u;
    mydiv_unsigned div_u (      //调用无符号除法器
    .aclk(clk),                                       // input wire aclk
    .s_axis_divisor_tvalid(divisor_tvalid_u),    // input wire s_axis_divisor_tvalid
    .s_axis_divisor_tready(divisor_tready_u),    // output wire s_axis_divisor_tready
    .s_axis_divisor_tdata(divisor_tdata_u),           // input wire [31 : 0] s_axis_divisor_tdata
    .s_axis_dividend_tvalid(dividend_tvalid_u),  // input wire s_axis_dividend_tvalid
    .s_axis_dividend_tready(dividend_tready_u),  // output wire s_axis_dividend_tready
    .s_axis_dividend_tdata(dividend_tdata_u),         // input wire [31 : 0] s_axis_dividend_tdata
    .m_axis_dout_tvalid(dout_tvalid_u),          // output wire m_axis_dout_tvalid
    .m_axis_dout_tdata(dout_tdata_u)             // output wire [63 : 0] m_axis_dout_tdata
    );

    wire [63:0] double_div_result = (exe_inst_div_w | exe_inst_mod_w) ? dout_tdata_s : dout_tdata_u;
    wire [31:0] div_result;
    assign div_result = (exe_inst_div_w | exe_inst_div_wu) ? double_div_result[63:32] : double_div_result[31:0];

//////////////////////////////////////////////////////////// * MEM * ////////////////////////////////////////////////////////////
    reg [31:0] mem_mul_result;
    reg mem_res_from_mul;

    reg [31:0] mem_div_result;
    reg mem_res_from_div;

    assign mem_ready_go      = 1'b1;                    //MEM级握手信号
    assign mem_allow         = ~mem_valid | mem_ready_go & wb_allow;   
    assign exe_to_mem_valid  = exe_valid & exe_ready_go;
    
    always @(posedge clk) begin                         //MEM级valid信号
        if(~resetn)
            mem_valid <= 1'b0;
        else
            mem_valid <= exe_to_mem_valid & mem_allow; 
    end

    always @(posedge clk) begin                 //PC
        if(~resetn) 
            mem_pc <= 1'b0;
        if(exe_to_mem_valid & mem_allow)begin
            mem_pc <= exe_pc;
        end
    end

    always @ (posedge clk)begin                 //结果选择信号（数据来自内存还是alu）
        if(~resetn)
            mem_res_from_mem <= 1'b0;
        if(exe_to_mem_valid & mem_allow) 
            mem_res_from_mem <= exe_res_from_mem;
    end

    always @ (posedge clk)begin                 //没有卵用的always块，zzh你最好删掉
        if(~resetn)
            mem_rkd_value <= 32'b0;
        if(exe_to_mem_valid & mem_allow) 
            mem_rkd_value <= exe_rkd_value;
    end

    always @ (posedge clk)begin                 //寄存器写相关信号
        if(~resetn)
            {mem_rf_we,mem_rf_waddr}<=6'b0;   
        if(exe_to_mem_valid & mem_allow) 
            {mem_rf_we,mem_rf_waddr} <= {exe_rf_we,exe_rf_waddr};
        else if(mem_to_wb_valid & wb_allow)
            {mem_rf_we,mem_rf_waddr} <= 6'b0;
    end

    assign mem_rf_wdata = mem_res_from_mem ? mem_result     :
                        mem_res_from_mul ? mem_mul_result :
                        mem_res_from_div ? mem_div_result :
                        mem_alu_result;

    always@(posedge clk)begin                   //alu计算结果
        if(~resetn)
            mem_alu_result <= 32'b0;
        if(exe_to_mem_valid & mem_allow)
            mem_alu_result <=exe_alu_result;     
    end

    always@(posedge clk)begin                   //乘法结果
        if(~resetn)
            mem_mul_result <= 32'b0;
            mem_res_from_mul <= 1'b0;
        if(exe_to_mem_valid & mem_allow)
            mem_mul_result <= exe_mul_result;
            mem_res_from_mul <= exe_res_from_mul;
    end

    always@(posedge clk)begin                   //除法结果
        if(~resetn)
            mem_div_result <= 32'b0;
            mem_res_from_div <= 1'b0;
        if(exe_to_mem_valid & mem_allow)
            mem_div_result <= div_result;
            mem_res_from_div <= exe_is_div;
    end

    assign data_sram_en    = exe_res_from_mem | exe_mem_we;      //数据RAM的相关信号
    assign data_sram_we    = {4{exe_mem_we}};
    assign data_sram_addr  = exe_alu_result;
    assign data_sram_wdata = exe_rkd_value;

    assign mem_result   = data_sram_rdata;

//////////////////////////////////////////////////////////// * WB * ////////////////////////////////////////////////////////////
    
    assign wb_ready_go      = 1'b1;                     //WB级握手信号
    assign wb_allow         = ~wb_valid | wb_ready_go ;     
    assign mem_to_wb_valid   = mem_valid & mem_ready_go;

    always @(posedge clk) begin                         //WB阶段valid信号
        if(~resetn)
            wb_valid <= 1'b0;
        else
            wb_valid <= mem_to_wb_valid & wb_allow; 
    end

    always @(posedge clk) begin             //PC
        if(~resetn)
            wb_pc <= 1'b0;
        if(mem_to_wb_valid & wb_allow) begin
            wb_pc <= mem_pc;
        end
    end

    always @(posedge clk) begin             //寄存器写相关信号
        if(~resetn)
            {wb_rf_we,wb_rf_waddr,wb_rf_wdata} <=38'b0;
        if(mem_to_wb_valid)
            {wb_rf_we,wb_rf_waddr,wb_rf_wdata} <= {mem_rf_we, mem_rf_waddr,mem_rf_wdata};
        else
            {wb_rf_we,wb_rf_waddr,wb_rf_wdata} <= 38'b0;
    end

    assign {rf_we,rf_waddr,rf_wdata} = {wb_rf_we,wb_rf_waddr,wb_rf_wdata};    
 

//////////////////////////////////////////////////////////// * debug info generate * ////////////////////////////////////////////////////////////// 
    assign debug_wb_pc       = wb_pc;
    assign debug_wb_rf_we   = {4{rf_we &wb_valid}};
    assign debug_wb_rf_wnum  = rf_waddr;
    assign debug_wb_rf_wdata = rf_wdata;

endmodule






