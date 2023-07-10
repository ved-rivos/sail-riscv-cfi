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
/*    Ved Shanbhogue                                                                     */
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
/* This file specifies the instructions in the 'Zicfilp' extension.   */
/* ****************************************************************** */
/* Forward-edge CFI: Landing pads */
function is_forward_cfi_active() -> bool = {
  if   not(haveZicfilp())
  then false
  else if cur_privilege == Machine 
  then mseccfg.MFCFIE() == 0b1
  else if cur_privilege == Supervisor 
  then menvcfg.SFCFIE() == 0b1
  else mstatus.UFCFIE() == 0b1
}
/* extension to jalr */
function zicfilp_update_elp(rs1_reg : regidx, rd_reg : regidx) -> unit = {
  /* 
   * c.jr expands to jalr x0, 0(rs1) and c.jalr expands to jalr x1, 0(rs1)
   * So only invocations from uncompressed jalr can result in sw guarded jumps
   */
  let is_sw_guarded_jump    : bool = ((rs1_reg == 0b00110) & (rd_reg == 0b00000));
  let is_indirect_call_jump : bool = (((rs1_reg != 0b00001) & (rs1_reg != 0b00101)));
  if is_indirect_call_jump == true & is_sw_guarded_jump == false & is_forward_cfi_active()
  then elp = ElpState_to_bits(LP_EXPECTED);
}
/* AUIPC with rd=x0 is a lpad instruction when zicfilp is active else a no-op */
function zicfilp_lpad( lpl : bits(20) ) -> Retired = {
   /* expected label is in x7 bits 31:12 */
   let  exp_lbl : bits(20) = x7[31..12];

   if   not(is_forward_cfi_active())
   then { RETIRE_SUCCESS }
   else if ( (lpl != exp_lbl) & (lpl != 0b00000000000000000000) & (elp == ElpState_to_bits(LP_EXPECTED)) )
   then { handle_illegal(); RETIRE_FAIL }
   else {elp = ElpState_to_bits(NO_LP_EXPECTED); RETIRE_SUCCESS };
}
/* trap delivery extension */
function zicfilp_trap_extension(del_priv : Privilege) -> unit = {
  let elp_val : elp_state = if is_forward_cfi_active() then elp else ElpState_to_bits(NO_LP_EXPECTED);

  match del_priv {
    Machine    => { mstatus = update_MPELP(mstatus, elp_val)},
    Supervisor => { mstatus = update_SPELP(mstatus, elp_val)},
    User       => { mstatus = update_SPELP(mstatus, elp_val)}
  };

  if haveZicfilp() then {
    elp = ElpState_to_bits(NO_LP_EXPECTED);
  }
}
/* extension to MRET */
function zicfilp_set_elp_to_mpelp() -> unit = {
  match is_forward_cfi_active() {
    true  => { elp = mstatus.MPELP() },
    false => { elp = ElpState_to_bits(NO_LP_EXPECTED) }
  };

  if haveZicfilp() then {
    mstatus = update_MPELP(mstatus, ElpState_to_bits(NO_LP_EXPECTED));
  }
}
/* extension to SRET */
function zicfilp_set_elp_to_spelp() -> unit = {
  match is_forward_cfi_active() {
    true  => { elp = mstatus.SPELP() },
    false => { elp = ElpState_to_bits(NO_LP_EXPECTED) }
  };

  if haveZicfilp() then {
    mstatus = update_SPELP(mstatus, ElpState_to_bits(NO_LP_EXPECTED));
  }
}
