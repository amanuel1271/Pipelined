/***************************************************************/
/*                                                             */
/*   MIPS-32 Instruction Level Simulator                       */
/*                                                             */
/*   CS311 KAIST                                               */
/*   run.c                                                     */
/*                                                             */
/***************************************************************/

#include <stdio.h>
#include "util.h"
#include "run.h"
#include "parse.h"

int flush = 0, take_pc = 0, end = 0, jump = 0;
int stall = 0, collision = 0, freak_acc = 0;
uint32_t save_index_1 = 0,save_index_2 = 0,save_value = 0;


int  write_to_reg(instruction* inst_to_exec,int* uses_rd_flag,int flag){ 

    short opcode = OPCODE(inst_to_exec);
    short funct_field = FUNC(inst_to_exec);
    unsigned char rd = RD(inst_to_exec);
    unsigned char rt = RT(inst_to_exec);

    switch(opcode)
    {
        case 0x0: 
            if (funct_field == 0x8)
            {
                *uses_rd_flag = -1;
                return NO_WRITE ;
            }
            *uses_rd_flag = 1;
            if (flag)
            {
                CURRENT_STATE.REGS[rd] = CURRENT_STATE.MEM_WB_ALU_OUT;
                return CURRENT_STATE.MEM_WB_ALU_OUT;
            }
            else
                return CURRENT_STATE.EX_MEM_ALU_OUT;
        case 0x2: 
        case 0x3: 
            if (opcode == 0x2)
            {
                *uses_rd_flag = -1;
                return NO_WRITE;
            }
            *uses_rd_flag = 2; 
            if (flag)
            {
                CURRENT_STATE.REGS[31] = CURRENT_STATE.MEM_WB_NPC + 4; 
                return CURRENT_STATE.MEM_WB_NPC + 4 ;
            }
            else
                return CURRENT_STATE.EX_MEM_NPC + 4;
        default:  
            if (opcode == 0x4 || opcode == 0x5 || opcode == 0x2B) 
            {
                *uses_rd_flag = -1;
                return NO_WRITE;
            }
            if (opcode == 0x23) 
            {
                if (flag)
                    CURRENT_STATE.REGS[rt] = CURRENT_STATE.MEM_WB_MEM_OUT;
                *uses_rd_flag = 0;
                return CURRENT_STATE.MEM_WB_MEM_OUT; 
            }
            else 
            {
                *uses_rd_flag = 0;
                if (flag)
                {
                    CURRENT_STATE.REGS[rt] = CURRENT_STATE.MEM_WB_ALU_OUT;
                    return CURRENT_STATE.MEM_WB_ALU_OUT;
                }
                else
                    return CURRENT_STATE.EX_MEM_ALU_OUT; 
            }
    }
}




void to_mem_forwarding_check_and_set_control()
{
  instruction* wb_inst  = CURRENT_STATE.MEM_WB_INST; 
  instruction* mem_inst = CURRENT_STATE.EX_MEM_INST; 
  if (OPCODE(wb_inst) == 0x23 && OPCODE(mem_inst) == 0x2B) 
  {
      unsigned char wb_rt = RT(wb_inst),mem_rt = RT(mem_inst);
      if ( (wb_rt == mem_rt) && wb_rt != 0) 
      {
        CURRENT_STATE.write_data_mem_source = 1; 
        CURRENT_STATE.MEM_WB_to_MEM_DATA_FORWARD_VALUE = CURRENT_STATE.MEM_WB_MEM_OUT;
      }
      else
        CURRENT_STATE.write_data_mem_source = 0; 
  }
  else
  {
    CURRENT_STATE.write_data_mem_source = 0; 
  }
}



void rd_and_source(int uses_rd,unsigned char reg, int *source,instruction* inst,int flag,int value)
{
    switch(uses_rd)
    {
        case 1: 
            if (reg == RD(inst) && reg != 0)
                *source = value;
            else
                if (flag || collision)
                    *source = 0;
            break;

        case 2: 
            if (reg == 31) 
                *source = value;
            else
                if (flag || collision)
                    *source = 0;
            break;
        case 0: 
            if (reg == RT(inst) && reg != 0)
                *source = value;
            else
                if (flag || collision)
                    *source = 0;
            break;
        default:
            if (flag || collision)
                *source = 0;
    }
}



void forwarding_check_mem_wb(int* first, int* second,int uses_rd)
{
    instruction* id_ex_inst  = CURRENT_STATE.ID_EX_INST;
    short opcode = OPCODE(id_ex_inst);
    short funct_field = FUNC(id_ex_inst);
    unsigned char rs = RS(id_ex_inst);

    switch(opcode)
    {
        case 0x0:   
            if (funct_field == 0x00 || funct_field == 0x02) 
            {
                *first = 0;
                unsigned char rt = RT(id_ex_inst); 
                rd_and_source(uses_rd,rt,second,CURRENT_STATE.MEM_WB_INST,1,1);
            }
            else 
            {
                unsigned char rs = RS(id_ex_inst);
                rd_and_source(uses_rd,rs,first,CURRENT_STATE.MEM_WB_INST,1,1);

                if (funct_field == 0x8) 
                    *second = 0;
                else
                {
                    unsigned char rt = RT(id_ex_inst); 
                    rd_and_source(uses_rd,rt,second,CURRENT_STATE.MEM_WB_INST,1,1);    
                }
            }
            break;
        case 0x2: 
        case 0x3: 
            *first = 0;
            *second = 0;
            break;
        default:
            if (opcode == 0xF) 
            {
                *first = 0;
                *second = 0;
            }
            else 
            {
                rd_and_source(uses_rd,rs,first,CURRENT_STATE.MEM_WB_INST,1,1);
                if (opcode == 0x2B || opcode == 0x4 || opcode == 0x5) 
                {
                    unsigned char rt = RT(id_ex_inst); 
                    rd_and_source(uses_rd,rt,second,CURRENT_STATE.MEM_WB_INST,1,1);
                }
                else 
                    *second = 0;
            }

    }
}



void forwarding_check_ex_mem(int* first, int* second,int uses_rd)
{
    instruction* id_ex_inst  = CURRENT_STATE.ID_EX_INST;
    short opcode = OPCODE(id_ex_inst);
    short funct_field = FUNC(id_ex_inst);
    unsigned char rs = RS(id_ex_inst);

    switch(opcode)
    {
        case 0x0: 
            if (funct_field == 0x00 || funct_field == 0x02) // if sll or srl, doesnt use rs
            {
                unsigned char rt = RT(id_ex_inst); // uses rt
                rd_and_source(uses_rd,rt,second,CURRENT_STATE.EX_MEM_INST,0,2);
            }
            else 
            {
                unsigned char rs = RS(id_ex_inst);
                rd_and_source(uses_rd,rs,first,CURRENT_STATE.EX_MEM_INST,0,2);
                if (funct_field == 0x8) 
                    ;
                else
                {
                    unsigned char rt = RT(id_ex_inst); 
                    rd_and_source(uses_rd,rt,second,CURRENT_STATE.EX_MEM_INST,0,2); 
                }
            }
            break;
        case 0x2:
        case 0x3:
            break;
        default: 
            if (opcode == 0xF) 
                ;
            else 
            {
                unsigned char rs = RS(id_ex_inst);
                rd_and_source(uses_rd,rs,first,CURRENT_STATE.EX_MEM_INST,0,2);
                if (opcode == 0x2B || opcode == 0x4 || opcode == 0x5) 
                {
                    unsigned char rt = RT(id_ex_inst); 
                    rd_and_source(uses_rd,rt,second,CURRENT_STATE.EX_MEM_INST,0,2);
                }
                else 
                    ;
            }
    }
}




void to_alu_forwarding_check_wb(int write,int uses_rd)
{
    int forwarding_index_1 = 0,forwarding_index_2 = 0;
    if (write == NO_WRITE) 
    {
        CURRENT_STATE.first_alu_source = 0;
        CURRENT_STATE.second_alu_source = 0;
    }
    else 
    {
        forwarding_check_mem_wb(&forwarding_index_1,&forwarding_index_2,uses_rd);
        if (forwarding_index_1 == 1) 
        {
            CURRENT_STATE.MEM_WB_ALU_FORWARD_VALUE = write; 
            CURRENT_STATE.first_alu_source = 1;
        }
        else if (forwarding_index_1 == 0)
            CURRENT_STATE.first_alu_source = 0;
        if (forwarding_index_2 == 1)
        {
            CURRENT_STATE.MEM_WB_ALU_FORWARD_VALUE = write; 
            CURRENT_STATE.second_alu_source = 1;
        }
        else if (forwarding_index_2 == 0)
            CURRENT_STATE.second_alu_source = 0;
    }
}



void to_alu_forwarding_check_ex()
{
    int forwarding_index_1 = 0,forwarding_index_2 = 0;
    int rd_use;
    instruction* ex_mem = CURRENT_STATE.EX_MEM_INST;
    int write_2 = write_to_reg(ex_mem,&rd_use,0); 
    if (write_2 != NO_WRITE)
    {
        forwarding_check_ex_mem(&forwarding_index_1,&forwarding_index_2,rd_use);
        if (forwarding_index_1 == 2) 
        {
            CURRENT_STATE.EX_MEM_ALU_FORWARD_VALUE = write_2; 
            CURRENT_STATE.first_alu_source = 2;
        }
        if (forwarding_index_2 == 2)
        {
            CURRENT_STATE.EX_MEM_ALU_FORWARD_VALUE = write_2; 
            CURRENT_STATE.second_alu_source = 2;
        }  
        if (collision)
        {
            CURRENT_STATE.first_alu_source = forwarding_index_1;
            CURRENT_STATE.second_alu_source = forwarding_index_2;
            collision = 0;
        }
    }
}


int stall_check()
{
    instruction* ex_mem = CURRENT_STATE.EX_MEM_INST;
    instruction* id_ex = CURRENT_STATE.ID_EX_INST;
    short op = OPCODE(ex_mem);
    
    if (op != 0x23) 
        return 0;
    unsigned char load_rt = RT(ex_mem);
    short opcode = OPCODE(id_ex);
    short func = FUNC(id_ex);

    switch(opcode)
    {
        case 0x0:
            if (func == 0x00 || func == 0x02) 
            {
                unsigned char rt = RT(id_ex);
                return (rt == load_rt);
            }
            else if(func == 0x8)
            {
                unsigned char rs = RS(id_ex);
                return (rs == load_rt);
            }
            else
            {
                unsigned char rt = RT(id_ex);
                unsigned char rs = RS(id_ex);
                return ( (rt == load_rt) || (load_rt == rs) );
            }
            break;
        case 0x2:
        case 0x3:
            return 0;
            break;
        default:
            if (opcode == 0xF) 
                return 0;
            else if (opcode == 0x4 || opcode == 0x5) 
            {
                unsigned char rt = RT(id_ex);
                unsigned char rs = RS(id_ex);
                return ( (rt == load_rt) || (load_rt == rs) );
            }
            else
            {
                unsigned char rs = RS(id_ex);
                return (rs == load_rt);
            }
    }
}

int handle_exceptions()
{
    if (flush)
    {
        flush = 0;
        return 1;
    }
    
    if (take_pc)
        take_pc = 0;
    
    if (jump)
    {
        jump = 0;
        CURRENT_STATE.PIPE[1] = 0;
        CURRENT_STATE.ID_EX_stall_or_no_inst = 1;
    }
    
    if (stall)
    {
        stall = 0;
        CURRENT_STATE.PIPE[2] = 0;
        return 1;
    }
    
    return 0;
    
}


void IF_Stage()
{
    uint32_t pc = CURRENT_STATE.PC;
    if (pc - MEM_TEXT_START >= text_size){
        CURRENT_STATE.PIPE[0] = 0;
        CURRENT_STATE.IF_ID_stall_or_no_inst = 1;
        if (CURRENT_STATE.PIPE[0] == 0 && CURRENT_STATE.PIPE[1] == 0 && CURRENT_STATE.PIPE[2] == 0)
            end = 1;
        return;
    }
    if (handle_exceptions())
        return;
    
    pc = CURRENT_STATE.PC;
    CURRENT_STATE.PIPE[0] = pc;
    instruction *inst = get_inst_info(pc);
    CURRENT_STATE.IF_ID_INST = inst;
    CURRENT_STATE.IF_ID_NPC = pc;
    CURRENT_STATE.IF_ID_stall_or_no_inst = 0;
    CURRENT_STATE.PC += 4;
}


void ID_Stage()
{
    if (stall)
        return;
    
    CURRENT_STATE.PIPE[1] = CURRENT_STATE.PIPE[0];
    CURRENT_STATE.ID_EX_stall_or_no_inst = CURRENT_STATE.IF_ID_stall_or_no_inst;
    
    if (CURRENT_STATE.IF_ID_stall_or_no_inst)
        return;
    
    short immediate = IMM(CURRENT_STATE.IF_ID_INST);
    CURRENT_STATE.ID_EX_IMM = SIGN_EX(immediate);
    CURRENT_STATE.ID_EX_ZERO_EXT_IMM = (unsigned short)immediate;
    CURRENT_STATE.ID_EX_INST = CURRENT_STATE.IF_ID_INST;
    CURRENT_STATE.ID_EX_NPC = CURRENT_STATE.IF_ID_NPC;
    unsigned char rs = RS(CURRENT_STATE.IF_ID_INST);
    unsigned char rt = RT(CURRENT_STATE.IF_ID_INST);
    CURRENT_STATE.ID_EX_REG1 = CURRENT_STATE.REGS[rs];
    CURRENT_STATE.ID_EX_REG2 = CURRENT_STATE.REGS[rt];

}




uint32_t execute_R(short funct_field,uint32_t alu_source_1,uint32_t alu_source_2,unsigned char shamt)
{
    uint32_t ALU_result;
    switch(funct_field)
    {
        case 0x21: 
            ALU_result = alu_source_1 + alu_source_2;
            break;
        case 0x24: 
            ALU_result = alu_source_1 & alu_source_2;
            break;
        case 0x27: 
            ALU_result = ~(alu_source_1 | alu_source_2);
            break;
        case 0x25: 
            ALU_result = alu_source_1 | alu_source_2;
            break;
        case 0x2B: 
            ALU_result = (alu_source_1 < alu_source_2)? TRUE : FALSE;
            break;
        case 0x00: 
            ALU_result =  alu_source_2 << shamt;
            break;
        case 0x02: 
            ALU_result =  alu_source_2 >> shamt;
            break;
        case 0x23: 
            ALU_result = alu_source_1 - alu_source_2;
            break;
    }
    return ALU_result;
        
}



uint32_t execute_I(uint32_t alu_source_1,short opcode, int sign_extended,uint32_t zero_extended)
{
    uint32_t ALU_result;
    switch(opcode)
    {
        case 0x9: 
            ALU_result = alu_source_1 + sign_extended;
            break;
        case 0xC: 
            ALU_result = alu_source_1 & zero_extended;
            break;
        case 0xF: 
            ALU_result = zero_extended << 16; 
            break;
        case 0xD: 
            ALU_result = alu_source_1 | zero_extended;   
            break;
        case 0xB: 
            ALU_result = (alu_source_1 < sign_extended)? TRUE : FALSE;
            break;  
        case 0x23: 
            ALU_result = sign_extended + alu_source_1;
            break;
        case 0x2B: 
            ALU_result = sign_extended + alu_source_1;
            break;
    }
    return ALU_result;
}



void Execute_ALU_write()
{
    int sign_extended = CURRENT_STATE.ID_EX_IMM;
    uint32_t zero_extended = CURRENT_STATE.ID_EX_ZERO_EXT_IMM;
    uint32_t alu_source_1,alu_source_2;

    switch(CURRENT_STATE.first_alu_source){
        case 0:
            alu_source_1 = CURRENT_STATE.ID_EX_REG1;
            break;
        case 1:
            alu_source_1 = CURRENT_STATE.MEM_WB_ALU_FORWARD_VALUE;
            break;
        default:
            alu_source_1 = CURRENT_STATE.EX_MEM_ALU_FORWARD_VALUE;
    }
    switch(CURRENT_STATE.second_alu_source)
    {
        case 0:
            alu_source_2 =  CURRENT_STATE.ID_EX_REG2;
            break;
        case 1:
            alu_source_2 = CURRENT_STATE.MEM_WB_ALU_FORWARD_VALUE;
            break;
        default:
            alu_source_2 = CURRENT_STATE.EX_MEM_ALU_FORWARD_VALUE;
    }
    if (freak_acc)
    {
        freak_acc = 0;
        if (save_index_1 == 1 && CURRENT_STATE.first_alu_source == 0)
            alu_source_1 = save_value;

        if (save_index_2 == 1 && CURRENT_STATE.second_alu_source == 0 )
            alu_source_2 = save_value;
    }

    uint32_t ALU_result; 
    uint32_t ALU_zero = 0;
    short opcode = OPCODE(CURRENT_STATE.ID_EX_INST);
    short funct_field = FUNC(CURRENT_STATE.ID_EX_INST);
    unsigned char shamt = (unsigned char)SHAMT(CURRENT_STATE.ID_EX_INST);
    uint32_t target  = TARGET(CURRENT_STATE.ID_EX_INST);
    uint32_t jump_target = (target << 2) & 0x0FFFFFFF;
    uint32_t upper_4_bits = (CURRENT_STATE.ID_EX_NPC + 4) & 0xF0000000;

    switch(opcode)
    {
        case 0x0:
            if (funct_field == 0x8) 
            {
                jump = 1;
                CURRENT_STATE.PC = alu_source_1; 
            }
            else
                ALU_result = execute_R(funct_field,alu_source_1,alu_source_2,shamt);
            break;
            
        case 0x2: 
        case 0x3:
            jump = 1;
            CURRENT_STATE.PC = upper_4_bits | jump_target;
            break;
        default:
            if (opcode ==  0x4) 
            {
                if (alu_source_1 == alu_source_2)
                    ALU_zero = 1;
            } 
            else if (opcode == 0x5 ) 
            {
                if (alu_source_1 != alu_source_2)
                    ALU_zero = 1;
            }
            else
                ALU_result = execute_I(alu_source_1,opcode,sign_extended,zero_extended);
    }

    CURRENT_STATE.EX_MEM_BR_TAKE = ALU_zero;
    CURRENT_STATE.EX_MEM_ALU_OUT = ALU_result;
    CURRENT_STATE.EX_MEM_BR_TARGET = CURRENT_STATE.ID_EX_NPC + 4 + (sign_extended << 2);
    CURRENT_STATE.EX_MEM_WRITE_VALUE =  alu_source_2;
}


void EX_Stage()
{
    CURRENT_STATE.PIPE[2] = CURRENT_STATE.PIPE[1];
    CURRENT_STATE.EX_MEM_stall_or_no_inst = CURRENT_STATE.ID_EX_stall_or_no_inst;
    
    if (CURRENT_STATE.ID_EX_stall_or_no_inst)
        return;
    if (stall)
    {
        CURRENT_STATE.EX_MEM_stall_or_no_inst = 1;
        return;
    }
    Execute_ALU_write();
    CURRENT_STATE.EX_MEM_NPC = CURRENT_STATE.ID_EX_NPC;
    CURRENT_STATE.EX_MEM_INST = CURRENT_STATE.ID_EX_INST;

}


void MEM_Stage()
{
    CURRENT_STATE.PIPE[3] = CURRENT_STATE.PIPE[2];
    CURRENT_STATE.MEM_WB_stall_or_no_inst = CURRENT_STATE.EX_MEM_stall_or_no_inst;

    if (CURRENT_STATE.EX_MEM_stall_or_no_inst)
        return;
    
    if (CURRENT_STATE.EX_MEM_BR_TAKE)
    {
        CURRENT_STATE.PIPE[0] = 0; CURRENT_STATE.IF_ID_stall_or_no_inst = 1;
        CURRENT_STATE.PIPE[1] = 0; CURRENT_STATE.ID_EX_stall_or_no_inst = 1;
        CURRENT_STATE.PIPE[2] = 0; CURRENT_STATE.EX_MEM_stall_or_no_inst = 1;
        CURRENT_STATE.PC = CURRENT_STATE.EX_MEM_BR_TARGET;
        flush = 1;
    }
    else
        flush = 0;
    if (stall_check()) 
    {
        stall = 1;
        freak_acc = 1;
        save_index_1 = CURRENT_STATE.first_alu_source;
        save_index_2 = CURRENT_STATE.second_alu_source;
        save_value = CURRENT_STATE.MEM_WB_ALU_FORWARD_VALUE;
    }

    to_alu_forwarding_check_ex();
    short opcode = OPCODE(CURRENT_STATE.EX_MEM_INST);
    uint32_t address = CURRENT_STATE.EX_MEM_ALU_OUT;

    if (opcode == 0x23) 
    {
        CURRENT_STATE.MEM_WB_MEM_OUT = mem_read_32(address); 
    }
    else if (opcode == 0x2B) 
    {
        uint32_t write_value;

        if (CURRENT_STATE.write_data_mem_source == 1)
            write_value =  CURRENT_STATE.MEM_WB_to_MEM_DATA_FORWARD_VALUE;
        else
            write_value = CURRENT_STATE.EX_MEM_WRITE_VALUE;
        mem_write_32(address,write_value);
    }
    CURRENT_STATE.MEM_WB_NPC = CURRENT_STATE.EX_MEM_NPC;
    CURRENT_STATE.MEM_WB_INST = CURRENT_STATE.EX_MEM_INST;
    CURRENT_STATE.MEM_WB_ALU_OUT = CURRENT_STATE.EX_MEM_ALU_OUT;
    CURRENT_STATE.MEM_WB_BR_TAKE = CURRENT_STATE.EX_MEM_BR_TAKE;
}



void WB_Stage()
{
    CURRENT_STATE.PIPE[4] = CURRENT_STATE.PIPE[3];

    if (CURRENT_STATE.MEM_WB_stall_or_no_inst) 
    {
        collision = 1;
        return;
    }
    collision = 0;

    if (CURRENT_STATE.MEM_WB_BR_TAKE)
        take_pc = 1;
    
    int uses_rd;
    int writes = write_to_reg(CURRENT_STATE.MEM_WB_INST,&uses_rd,1); 
    to_mem_forwarding_check_and_set_control();
    to_alu_forwarding_check_wb(writes,uses_rd);
    INSTRUCTION_COUNT++;

    if (end)
        RUN_BIT = FALSE;
}



instruction* get_inst_info(uint32_t pc) { 
    return &INST_INFO[(pc - MEM_TEXT_START) >> 2];
}




void process_instruction(){
    WB_Stage();
    MEM_Stage();
    EX_Stage();
    ID_Stage();
    IF_Stage();
}
