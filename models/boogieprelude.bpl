// var mem: [bv64]bv8;
// var pc: bv64;
// var exception: bv64;
// var returned: bool;
// var current_priv: bv2;

// Arithmetic
function {:bvbuiltin "bvadd"} bv32add(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} bv64add(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} bv64sub(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} bv64mul(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} bv64udiv(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} bv64urem(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsdiv"} bv64sdiv(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsrem"} bv64srem(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsmod"} bv64smod(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvneg"} bv64neg(bv64) returns(bv64);

// Bitwise operations
function {:bvbuiltin "bvand"} bv64and(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} bv64or(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvnot"} bv64not(bv64) returns(bv64);
function {:bvbuiltin "bvxor"} bv64xor(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvnand"} bv64nand(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvnor"} bv64nor(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxnor"} bv64xnor(bv64,bv64) returns(bv64);

// Bit shifting
function {:bvbuiltin "bvshl"} bv64shl(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} bv32shl(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} bv32lshr(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} bv64lshr(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvashr"} bv32ashr(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvashr"} bv64ashr(bv64,bv64) returns(bv64);

// Unsigned comparison
function {:bvbuiltin "bvult"} bv2ult(bv2,bv2) returns(bool);
function {:bvbuiltin "bvult"} bv64ult(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} bv64ule(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} bv64ugt(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} bv64uge(bv64,bv64) returns(bool);

// Signed comparison
function {:bvbuiltin "bvslt"} bv64slt(bv64,bv64) returns(bool);
function {:bvbuiltin "bvsle"} bv64sle(bv64,bv64) returns(bool);
function {:bvbuiltin "bvsgt"} bv64sgt(bv64,bv64) returns(bool);
function {:bvbuiltin "bvsge"} bv64sge(bv64,bv64) returns(bool);

// Zero extension
function {:bvbuiltin "zero_extend 27"} bv5_zero_extend27(bv5) : bv32;
function {:bvbuiltin "zero_extend 32"} bv32_zero_extend32(bv32) : bv64;
function {:bvbuiltin "zero_extend 48"} bv16_zero_extend48(bv16) : bv64;
function {:bvbuiltin "zero_extend 56"} bv8_zero_extend56(bv8) : bv64;
function {:bvbuiltin "zero_extend 59"} bv5_zero_extend59(bv5) : bv64;

// Signed extension
function {:bvbuiltin "sign_extend 32"} bv32_sign_extend32(bv32) : bv64;
function {:bvbuiltin "sign_extend 48"} bv16_sign_extend48(bv16) : bv64;
function {:bvbuiltin "sign_extend 56"} bv8_sign_extend56(bv8) : bv64;

// Loads values from byte-sized memory
function {:inline} loadByte_macro (mem: [bv64]bv8, addr: bv64): bv8 {
  mem[addr]
}
function {:inline} loadHalf_macro (mem: [bv64]bv8, addr: bv64): bv16 {
  (loadByte_macro(mem, bv64add(addr, 1bv64)) ++ loadByte_macro(mem, addr))
}
function {:inline} loadWord_macro (mem: [bv64]bv8, addr: bv64): bv32 
{
  (loadHalf_macro(mem, bv64add(addr, 2bv64)) ++ loadHalf_macro(mem, addr))
}
function {:inline} loadDouble_macro (mem: [bv64]bv8, addr: bv64): bv64 {
  (loadWord_macro(mem, bv64add(addr, 4bv64)) ++ loadWord_macro(mem, addr))
}
// Aliases to the load value macros above
function {:inline} deref_1(mem: [bv64]bv8, addr: bv64): bv8 {
  loadByte_macro(mem, addr)
}
function {:inline} deref_2(mem: [bv64]bv8, addr: bv64): bv16 {
  loadHalf_macro(mem, addr)
}
function {:inline} deref_4(mem: [bv64]bv8, addr: bv64): bv32 {
  loadWord_macro(mem, addr)
}
function {:inline} deref_8(mem: [bv64]bv8, addr: bv64): bv64
{
  loadDouble_macro(mem, addr)
}
// Memory updates to byte-sized memory
function {:inline} mem_update_byte(memP: [bv64]bv8, index: bv64, value: bv8): [bv64]bv8 {
  memP[index := value]
}
function {:inline} mem_update_half(memP: [bv64]bv8, index: bv64, value: bv16): [bv64]bv8 {
  mem_update_byte(mem_update_byte(memP, index, value[8:0]), bv64add(index, 1bv64), value[16:8])
}
function {:inline} mem_update_word(memP: [bv64]bv8, index: bv64, value: bv32): [bv64]bv8 {
  mem_update_half(mem_update_half(memP, index, value[16:0]), bv64add(index,2bv64), value[32:16])
}
function {:inline} mem_update_double(memP: [bv64]bv8, index: bv64, value: bv64): [bv64]bv8 {
  mem_update_word(mem_update_word(memP, index, value[32:0]), bv64add(index,4bv64), value[64:32])
}
// Instruction specifications
procedure {:inline 1} amoswap_w_aq_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} amoor_w_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} amoor_w_aq_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} add_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64add(rs1, rs2); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sub_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64sub(rs1, rs2); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
// TODO: Check semantics
procedure {:inline 1} mul_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64mul(rs1, rs2); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
// FIXME: Implement
procedure {:inline 1} div_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := 0bv64; // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
// FIXME: Implement
procedure {:inline 1} rem_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := 0bv64; // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sll_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64shl(bv64and(rs2, 63bv64), rs1); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} slt_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    if(bv64slt(rs1, rs2))
      {
        ret := 1bv64; // line 0
      }
    else
      {
        ret := 0bv64; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sltu_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    if(bv64ult(rs1, rs2))
      {
        ret := 1bv64; // line 0
      }
    else
      {
        ret := 0bv64; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} xor_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64xor(rs1, rs2); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} srl_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64lshr(bv64and(rs2, 63bv64), rs1); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sra_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64ashr(bv64and(rs2, 63bv64), rs1); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} or_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64or(rs1, rs2); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} and_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64and(rs1, rs2); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} addw_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32((bv64add(rs1, rs2))[32:0]); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} subw_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32((bv64sub(rs1, rs2))[32:0]); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sllw_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32shl(bv5_zero_extend27((rs2)[5:0]), (rs1)[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} srlw_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32lshr(bv5_zero_extend27((rs2)[5:0]), (rs1)[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sraw_proc(rs1: bv64, rs2: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32ashr(bv5_zero_extend27((rs2)[5:0]), (rs1)[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} jalr_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc, returned;
  {
    ret := bv64add(pc, 4bv64); // line 0
    returned := true;
    pc := (bv64add(rs1, imm)[64:1] ++ 0bv1); // line 0
  }
procedure {:inline 1} mret_proc()
  modifies pc;
  {
    // FIXME: Fill out the actual specs of this instruction.
    pc := 0bv64;
  }
procedure {:inline 1} lb_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv8_sign_extend56(loadByte_macro(mem, bv64add(rs1, imm))); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} lh_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv16_sign_extend48(loadHalf_macro(mem, bv64add(rs1, imm))); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} lw_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(loadWord_macro(mem, bv64add(rs1, imm))); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} lbu_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv8_zero_extend56(loadByte_macro(mem, bv64add(rs1, imm))); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} lhu_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv16_zero_extend48(loadHalf_macro(mem, bv64add(rs1, imm))); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} addi_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64add(rs1, imm); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} slti_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    if(bv64slt(rs1, imm))
      {
        ret := 1bv64; // line 0
      }
    else
      {
        ret := 0bv64; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sltiu_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    if(bv64ult(rs1, imm))
      {
        ret := 1bv64; // line 0
      }
    else
      {
        ret := 0bv64; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} xori_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64xor(rs1, imm); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} ori_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64or(rs1, imm); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} andi_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64and(rs1, imm); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} slli_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc, exception;
  {
    if(!(bv64ult(imm, 64bv64)))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        ret := bv64shl(imm, rs1); // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} srli_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc, exception;
  {
    if(!(bv64ult(imm, 64bv64)))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        ret := bv64lshr(imm, rs1); // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} srai_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc, exception;
  {
    if(!(bv64ult(imm, 64bv64)))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        ret := bv64ashr(imm, rs1); // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
// FIXME: Implement wfi instruction 
procedure {:inline 1} wfi_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64);
  }
procedure {:inline 1} fence_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} fence_i_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sfence_vma_proc()
  modifies pc;
  {
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} lwu_proc(rs1 :bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_zero_extend32(loadWord_macro(mem, bv64add(rs1, imm))); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} ld_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := loadDouble_macro(mem, bv64add(rs1, imm)); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} addiw_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32add(rs1[32:0], imm[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} slliw_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32shl((imm)[32:0], (rs1)[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} srliw_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32lshr((imm)[32:0], (rs1)[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sraiw_proc(rs1: bv64, imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv32_sign_extend32(bv32ashr((imm)[32:0], (rs1)[32:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sb_proc(rs1: bv64, imm: bv64, rs2: bv64) returns ()
  modifies pc, mem;
  {
    mem[bv64add(rs1, imm)] := rs2[8:0]; // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sh_proc(rs1: bv64, imm: bv64, rs2: bv64) returns ()
  modifies pc, mem;
  {
    mem[bv64add(rs1, imm)] := rs2[8:0];
    mem[bv64add(rs1, bv64add(imm, 1bv64))] := rs2[16:8];
    pc := bv64add(pc, 4bv64);
  }
procedure {:inline 1} sw_proc(rs1: bv64, imm: bv64, rs2: bv64) returns ()
  modifies pc, mem;
  {
    mem[bv64add(rs1, imm)] := rs2[8:0];
    mem[bv64add(rs1, bv64add(imm, 1bv64))] := rs2[16:8];
    mem[bv64add(rs1, bv64add(imm, 2bv64))] := rs2[24:16];
    mem[bv64add(rs1, bv64add(imm, 3bv64))] := rs2[32:24];
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} sd_proc(rs1: bv64, imm: bv64, rs2: bv64) returns ()
  modifies pc, mem;
  {
    mem[bv64add(rs1, imm)] := rs2[8:0];
    mem[bv64add(rs1, bv64add(imm, 1bv64))] := rs2[16:8];
    mem[bv64add(rs1, bv64add(imm, 2bv64))] := rs2[24:16];
    mem[bv64add(rs1, bv64add(imm, 3bv64))] := rs2[32:24];
    mem[bv64add(rs1, bv64add(imm, 4bv64))] := rs2[40:32];
    mem[bv64add(rs1, bv64add(imm, 5bv64))] := rs2[48:40];
    mem[bv64add(rs1, bv64add(imm, 6bv64))] := rs2[56:48];
    mem[bv64add(rs1, bv64add(imm, 7bv64))] := rs2[64:56];
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} beq_proc(rs1: bv64, rs2: bv64, imm: bv64) returns ()
  modifies pc;
  {
    if((rs1 == rs2))
      {
        pc := imm; // line 0
      }
    else
      {
        pc := bv64add(pc, 4bv64); // line 0
      }
  }
procedure {:inline 1} bne_proc(rs1: bv64, rs2: bv64, imm: bv64) returns ()
  modifies pc;
  {
    if(!((rs1 == rs2)))
      {
        pc := imm; // line 0
      }
    else
      {
        pc := bv64add(pc, 4bv64); // line 0
      }
  }
procedure {:inline 1} blt_proc(rs1: bv64, rs2: bv64, imm: bv64) returns ()
  modifies pc;
  {
    if(bv64slt(rs1, rs2))
      {
        pc := imm; // line 0
      }
    else
      {
        pc := bv64add(pc, 4bv64); // line 0
      }
  }
procedure {:inline 1} bge_proc(rs1: bv64, rs2: bv64, imm: bv64) returns ()
  modifies pc;
  {
    if(!(bv64slt(rs1, rs2)))
      {
        pc := imm; // line 0
      }
    else
      {
        pc := bv64add(pc, 4bv64); // line 0
      }
  }
procedure {:inline 1} bltu_proc(rs1: bv64, rs2: bv64, imm: bv64) returns ()
  modifies pc;
  {
    if(bv64ult(rs1, rs2))
      {
        pc := imm; // line 0
      }
    else
      {
        pc := bv64add(pc, 4bv64); // line 0
      }
  }
procedure {:inline 1} bgeu_proc(rs1: bv64, rs2: bv64, imm: bv64) returns ()
  modifies pc;
  {
    if(!(bv64ult(rs1, rs2)))
      {
        pc := imm; // line 0
      }
    else
      {
        pc := bv64add(pc, 4bv64); // line 0
      }
  }
procedure {:inline 1} lui_proc(imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret :=  bv32_sign_extend32(bv32shl(12bv32, 0bv12 ++ imm[20:0])); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} auipc_proc(imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64add(pc, bv64shl(12bv64, imm)); // line 0
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} jal_proc(imm: bv64) returns (ret: bv64)
  modifies pc;
  {
    ret := bv64add(pc, 4bv64); // line 0
    pc := imm; // line 0
  }
procedure {:inline 1} csrrw_proc(csr: bv64, rs1: bv64) returns (csr_ret: bv64, rd_ret: bv64)
  modifies pc, exception;
  {
    if((bv2ult(current_priv, (csr)[10:8]) || (bv64ult(0bv64, rs1) && !(bv2ult((csr)[12:10], 3bv2)))))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        csr_ret, rd_ret := rs1, csr; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} csrrs_proc(csr: bv64, rs1: bv64) returns (csr_ret: bv64, rd_ret: bv64)
  modifies pc, exception;
  {
    if((bv2ult(current_priv, (csr)[10:8]) || (bv64ult(0bv64, rs1) && !(bv2ult((csr)[12:10], 3bv2)))))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        csr_ret, rd_ret := bv64or(rs1, csr), csr; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} csrrc_proc(csr: bv64, rs1: bv64) returns (csr_ret: bv64, rd_ret: bv64)
  modifies pc, exception;
  {
    if((bv2ult(current_priv, (csr)[10:8]) || (bv64ult(0bv64, rs1) && !(bv2ult((csr)[12:10], 3bv2)))))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        csr_ret, rd_ret := bv64and(rs1, csr), csr; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} csrrwi_proc(csr: bv64, imm: bv64) returns (csr_ret: bv64, rd_ret: bv64)
  modifies pc, exception;
  {
    if((bv2ult(current_priv, (csr)[10:8]) || (true && !(bv2ult((csr)[12:10], 3bv2)))))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        csr_ret, rd_ret := bv5_zero_extend59(imm[5:0]), csr; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} csrrsi_proc(csr: bv64, imm: bv64) returns (csr_ret: bv64, rd_ret: bv64)
  modifies pc, exception;
  {
    if((bv2ult(current_priv, (csr)[10:8]) || (true && !(bv2ult((csr)[12:10], 3bv2)))))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        csr_ret, rd_ret := bv64or(bv5_zero_extend59(imm[5:0]), csr), csr; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
procedure {:inline 1} csrrci_proc(csr: bv64, imm: bv64) returns (csr_ret: bv64, rd_ret: bv64)
  modifies pc, exception;
  {
    if((bv2ult(current_priv, (csr)[10:8]) || (true && !(bv2ult((csr)[12:10], 3bv2)))))
      {
        exception := 2bv64; // line 0
      }
    else
      {
        csr_ret, rd_ret := bv64and((bv5_zero_extend59(imm[5:0])), csr), csr; // line 0
      }
    pc := bv64add(pc, 4bv64); // line 0
  }
  
