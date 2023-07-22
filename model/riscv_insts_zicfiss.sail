/*=======================================================================================*/
/*  RISCV Sail Model                                                                     */
/*                                                                                       */
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except for the snapshots of the Lem and Sail libraries                   */
/*  in the prover_snapshots directory (which include copies of their                     */
/*  licences), is subject to the BSD two-clause licence below.                           */
/*                                                                                       */
/*  Copyright (c) 2017-2023                                                              */
/*    Prashanth Mundkur                                                                  */
/*    Rishiyur S. Nikhil and Bluespec, Inc.                                              */
/*    Jon French                                                                         */
/*    Brian Campbell                                                                     */
/*    Robert Norton-Wright                                                               */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Shaked Flur                                                                        */
/*    Christopher Pulte                                                                  */
/*    Peter Sewell                                                                       */
/*    Alexander Richardson                                                               */
/*    Hesham Almatary                                                                    */
/*    Jessica Clarke                                                                     */
/*    Microsoft, for contributions by Robert Norton-Wright and Nathaniel Wesley Filardo  */
/*    Peter Rugg                                                                         */
/*    Aril Computer Corp., for contributions by Scott Johnson                            */
/*    Philipp Tomsich                                                                    */
/*    VRULL GmbH, for contributions by its employees                                     */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by the above within the Rigorous                         */
/*  Engineering of Mainstream Systems (REMS) project, partly funded by                   */
/*  EPSRC grant EP/K008528/1, at the Universities of Cambridge and                       */
/*  Edinburgh.                                                                           */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* ****************************************************************** */
/* This file specifies the instructions in the 'Zicfiss' extension.   */
/* ****************************************************************** */
/* Backward-edge CFI: Shadow stack */
union clause ast = ZICFISSLP_SSLOAD    : (regidx)
union clause ast = ZICFISSLP_SSPOPCHK  : (regidx)
union clause ast = ZICFISSLP_SSPINC    : (bits(5))
union clause ast = ZICFISSLP_SSPRR     : (regidx)
union clause ast = ZICFISSLP_SSPUSH    : (regidx)
union clause ast = ZICFISSLP_SSAMOSWAP : (regidx, regidx, regidx)

mapping clause encdec = ZICFISSLP_SSLOAD(0b00001)
  <-> 0b100000011100 @ 0b00000 @ 0b100 @ 0b00001 @ 0b1110011
mapping clause encdec = ZICFISSLP_SSLOAD(0b00101)
  <-> 0b100000011100 @ 0b00000 @ 0b100 @ 0b00101 @ 0b1110011
mapping clause encdec = ZICFISSLP_SSPOPCHK(0b00001)
  <-> 0b100000011100 @ 0b00001 @ 0b100 @ 0b00000 @ 0b1110011
mapping clause encdec = ZICFISSLP_SSPOPCHK(0b00101)
  <-> 0b100000011100 @ 0b00101 @ 0b100 @ 0b00000 @ 0b1110011
mapping clause encdec = ZICFISSLP_SSPINC(nzuimm)
      if nzuimm != 0b00000
  <-> 0b100000011101 @ nzuimm : bits(5) @ 0b100 @ 0b00000 @ 0b1110011
      if nzuimm != 0b00000
mapping clause encdec = ZICFISSLP_SSPRR(rd)
  <-> 0b100000011101 @ 0b00000 @ 0b100 @ rd @ 0b1110011

mapping clause encdec = ZICFISSLP_SSPUSH(0b00001)
  <-> 0b1000001 @ 0b00001 @ 0b00000 @ 0b100 @ 0b00000 @ 0b1110011
mapping clause encdec = ZICFISSLP_SSPUSH(0b00101)
  <-> 0b1000001 @ 0b00101 @ 0b00000 @ 0b100 @ 0b00000 @ 0b1110011
mapping clause encdec = ZICFISSLP_SSAMOSWAP(rs2, rs1, rd)
  <-> 0b1000001 @ rs2 @ rs1 @ 0b100 @ rd @ 0b1110011

mapping clause assembly = ZICFISSLP_SSLOAD(rd)
  <-> "ssload" ^ spc() ^ reg_name(rd)
mapping clause assembly = ZICFISSLP_SSPOPCHK(rs1)
  <-> "sspopchk" ^ spc() ^ reg_name(rs1)
mapping clause assembly = ZICFISSLP_SSPINC(nzuimm)
      if nzuimm != 0b00000
  <-> "sspinc" ^ spc() ^ hex_bits_5(nzuimm)
      if nzuimm != 0b00000
mapping clause assembly = ZICFISSLP_SSPUSH(rs2)
  <-> "sspush" ^ spc() ^ reg_name(rs2)
mapping clause assembly = ZICFISSLP_SSAMOSWAP(rs2, rs1, rd)
  <-> "ssamoswap" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

union clause ast = C_ZICFISSLP_SSPUSH   : (regidx)
union clause ast = C_ZICFISSLP_SSPOPCHK : (regidx)
mapping clause encdec_compressed = C_ZICFISSLP_SSPUSH(0b00001)
  <-> 0b011 @ 0b0 @ 0b00001 @ 0b00000 @ 0b01
mapping clause encdec_compressed = C_ZICFISSLP_SSPOPCHK(0b00101)
  <-> 0b011 @ 0b0 @ 0b01001 @ 0b00000 @ 0b01
mapping clause assembly = C_ZICFISSLP_SSPUSH(rs1)
  <-> "c.sspush" ^ spc() ^ reg_name(rs1)
mapping clause assembly = C_ZICFISSLP_SSPOPCHK(rs1)
  <-> "c.sspopchk" ^ spc() ^ reg_name(rs1)

function is_backward_cfi_active() -> bool = {
  if   cur_privilege == Machine 
  then true
  else if cur_privilege == Supervisor 
  then menvcfg.SBCFIE() == 0b1
  else mstatus.UBCFIE() == 0b1
}

function check_ssp_misaligned(vaddr : xlenbits, width : word_width) -> bool = {
  ((width == WORD)   & (vaddr[0] == bitone | vaddr[1] == bitone)) |
  ((width == DOUBLE) & (vaddr[0] == bitone | vaddr[1] == bitone   | vaddr[2] == bitone))
}

function ss_load(vaddr : xlenbits, width : word_width) -> MemoryOpResult(xlenbits) = {
  if check_ssp_misaligned(vaddr, width)
  then MemException(E_Load_Access_Fault())
  else match translateAddr(vaddr, SSRead(Data)) {
    TR_Failure(e, _) => MemException(e),
    TR_Address(paddr, _) => {
      let mval : MemoryOpResult(xlenbits) = match sizeof(xlen) {
          32 => mem_read(SSRead(Data), paddr, 4, false, false, false),
          64 => mem_read(SSRead(Data), paddr, 8, false, false, false),
          _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
        };
        mval
      }
  }
}

function clause execute (ZICFISSLP_SSLOAD(rd)) = {
  if not(is_backward_cfi_active())
  then { X(rd) = X(0); RETIRE_SUCCESS }
  else {
    let addr  : xlenbits   = ssp;
    let width : word_width = match sizeof(xlen) {
        32 => WORD,
        64 => DOUBLE,
        _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
      };
    let mval  : MemoryOpResult(xlenbits) = ss_load(addr, width);
    match mval {
      MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL },
      MemValue(loaded) => { X(rd) = loaded; RETIRE_SUCCESS }
    }
  }
}

function clause execute (ZICFISSLP_SSPOPCHK(rs1)) = {
  if not(is_backward_cfi_active())
  then { RETIRE_SUCCESS }
  else {
    let addr : xlenbits = ssp;
    let width : word_width = match sizeof(xlen) {
        32 => WORD,
        64 => DOUBLE,
        _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
      };
    let mval : MemoryOpResult(xlenbits) = ss_load(addr, width);
    match (mval) {
      MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL },
      MemValue(loaded) => {
        if X(rs1) != loaded 
        then { handle_illegal(); RETIRE_FAIL }
        else {
          ssp = match width {
            WORD   => ssp + 4,
            DOUBLE => ssp + 8,
            _      => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
          };
          RETIRE_SUCCESS
        }
      }
    }
  }
}

function clause execute (C_ZICFISSLP_SSPOPCHK(rs1)) = {
  execute(ZICFISSLP_SSPOPCHK(rs1))
}

function clause execute (ZICFISSLP_SSPINC(nzuimm)) = {
  if not(is_backward_cfi_active())
  then { RETIRE_SUCCESS }
  else {
    let width : word_width = match sizeof(xlen) {
        32 => WORD,
        64 => DOUBLE,
        _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
      };
    ssp = match width {
        WORD   => ssp + EXTZ(nzuimm @ 0b00),
        DOUBLE => ssp + EXTZ(nzuimm @ 0b000),
        _      => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
      };
    RETIRE_SUCCESS
  }
}

function clause execute (ZICFISSLP_SSPRR(rd)) = {
  if not(is_backward_cfi_active()) 
  then { X(rd) = X(0) }
  else { X(rd) = ssp  };
  RETIRE_SUCCESS
}

function clause execute (ZICFISSLP_SSPUSH(rs2)) = {
  if not(is_backward_cfi_active())
  then { RETIRE_SUCCESS }
  else {
    let rs2_val : xlenbits = X(rs2);
    let width   : word_width = match sizeof(xlen) {
        32 => WORD,
        64 => DOUBLE,
        _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
      };
    let sta     : xlenbits = match width {
        WORD   => ssp - 4,
        DOUBLE => ssp - 8,
        _      => internal_error(__FILE__, __LINE__, "Unexpected xlen")
      };
    if check_ssp_misaligned(sta, width)
    then { handle_mem_exception(sta, E_SAMO_Access_Fault()); RETIRE_FAIL }
    else match translateAddr(sta, SSWrite(Data)) {
      TR_Failure(e, _)    => { handle_mem_exception(sta, e); RETIRE_FAIL },
      TR_Address(paddr, _) => {
        let eares : MemoryOpResult(unit) = match width {
          WORD   => mem_write_ea(paddr, 4, false, false, false),
          DOUBLE => mem_write_ea(paddr, 8, false, false, false),
          _      => internal_error(__FILE__, __LINE__, "unexpected width")
        };
        match (eares) {
          MemException(e) => { handle_mem_exception(sta, e); RETIRE_FAIL },
          MemValue(_) => {
            let wval : MemoryOpResult(bool) = match sizeof(xlen) {
              32 => mem_write_value(paddr, 4, rs2_val, false, false, false),
              64 => mem_write_value(paddr, 8, rs2_val, false, false, false),
              _  => internal_error(__FILE__, __LINE__, "unexpected width")
            };
            match wval {
              MemValue(true)  => { ssp = sta; RETIRE_SUCCESS },
              MemValue(false) => internal_error(__FILE__, __LINE__, "sspush got false from mem_write_value"),
              MemException(e) => { handle_mem_exception(sta, e); RETIRE_FAIL }
            };
          }
        }
      }
    }
  }
}
function clause execute (C_ZICFISSLP_SSPUSH(rs1)) = {
  execute(ZICFISSLP_SSPUSH(rs1))
}

function clause execute (ZICFISSLP_SSAMOSWAP(rs2, rs1, rd)) = {
  if not(is_backward_cfi_active()) 
  then { X(rd) = X(0); RETIRE_SUCCESS }
  else {
    let swap  : xlenbits   = X(rs2);
    let vaddr : xlenbits   = X(rs1);
    let width : word_width = match sizeof(xlen) {
        32 => WORD,
        64 => DOUBLE,
        _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
      };
    if check_ssp_misaligned(vaddr, width)
    then { handle_mem_exception(vaddr, E_SAMO_Access_Fault()); RETIRE_FAIL }
    else match translateAddr(vaddr, SSReadWrite(Data, Data)) {
      TR_Failure(e, _) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
      TR_Address(addr, _) => {
        let eares : MemoryOpResult(unit) = match width {
          WORD   => mem_write_ea(addr, 4, true & true, true, true),
          DOUBLE => mem_write_ea(addr, 8, true & true, true, true),
          _      => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
        };
        match (eares) {
          MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL },
          MemValue(_) => {
            let mval : MemoryOpResult(xlenbits) = match sizeof(xlen) {
              32 => mem_read(SSReadWrite(Data, Data), addr, 4, true, true, true),
              64 => mem_read(SSReadWrite(Data, Data), addr, 8, true, true, true),
              _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
            };
            match (mval) {
              MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL },
              MemValue(loaded) => {
                let wval   : MemoryOpResult(bool) = match sizeof(xlen) {
                  32 => mem_write_value(addr, 4, swap, true, true, true),
                  64 => mem_write_value(addr, 8, swap, true, true, true),
                  _  => internal_error(__FILE__, __LINE__, "Unexpected xlen width")
                };
                match (wval) {
                  MemValue(true)  => { X(rd) = loaded; RETIRE_SUCCESS },
                  MemValue(false) => { internal_error(__FILE__, __LINE__, "SSAMOSWAP got false from mem_write_value") },
                  MemException(e) => { handle_mem_exception(addr, e); RETIRE_FAIL }
                }
              }
            }
          }
        }
      }
    }
  }
}
