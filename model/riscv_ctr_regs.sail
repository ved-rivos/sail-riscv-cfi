/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Support CTR depths - if bit n is set then CTR depth 2^n is supported */
val sys_valid_ctr_depth = {c: "sys_valid_ctr_depth", ocaml: "Platform.valid_ctr_depth", _: "sys_valid_ctr_depth"} : unit -> bits(64)

/* Architectural state for the Ssctr and Smctr standard extension. */
bitfield Mctrctl : bits(64) = {
  DIRLJMPINH : 47,
  INDLJMPINH : 46,
  RETINH     : 45,
  CORSWAPINH : 44,
  DIRJMPINH  : 43,
  INDJMPINH  : 42,
  DIRCALLINH : 41,
  INDCALLINH : 40,
  TKBRINH    : 37,
  NTBREN     : 36,
  TRETINH    : 35,
  INTRINH    : 34,
  EXCINH     : 33,

  LCOFIFRZ   : 12,
  BPFRZ      : 11,

  MTE        : 9,
  STE        : 8,

  RASEMU     : 7,

  M          : 2,
  S          : 1,
  U          : 0
}
bitfield Sctrctl : bits(64) = {
  DIRLJMPINH : 47,
  INDLJMPINH : 46,
  RETINH     : 45,
  CORSWAPINH : 44,
  DIRJMPINH  : 43,
  INDJMPINH  : 42,
  DIRCALLINH : 41,
  INDCALLINH : 40,
  TKBRINH    : 37,
  NTBREN     : 36,
  TRETINH    : 35,
  INTRINH    : 34,
  EXCINH     : 33,

  LCOFIFRZ   : 12,
  BPFRZ      : 11,

  STE        : 8,

  RASEMU     : 7,

  S          : 1,
  U          : 0
}
bitfield Sctrdepth : bits(32) = {
  DEPTH      : 2 .. 0
}
bitfield Sctrstatus : bits(32) = {
  FROZEN     : 31,
  WRPTR      : 7 .. 0
}
bitfield Ctrsource : xlenbits = {
  PC         : xlen - 1 .. 1,
  V          : 0
}
bitfield Ctrtarget : xlenbits = {
  PC         : xlen - 1 .. 1,
  MISP       : 0
}
bitfield Ctrdata : bits(64) = {
  CCE        : 31 .. 28,
  CCM        : 27 .. 16,
  CCV        : 15,
  TYPE       : 3 .. 0
}

register sctrstatus : Sctrstatus
register sctrdepth  : Sctrdepth
register mctrctl    : Mctrctl
register ctrsource  : vector(256, dec, Ctrsource)
register ctrtarget  : vector(256, dec, Ctrtarget)
register ctrdata    : vector(256, dec, Ctrdata)
/* Should parameterize the cycle counter to support wider counters */
register ctr_cycle_counter : bits(13)
register ctr_cycle_counter_valid : bool

function legalize_mctrctl(o : Mctrctl, v : xlenbits) -> Mctrctl = {
  let m : Mctrctl = Mk_Mctrctl(zero_extend(v));
  m
}

function lower_sctrctl(m : Mctrctl) -> Sctrctl = {
  let s = Mk_Sctrctl(m.bits);
  s
}

function legalize_sctrctl(m : Mctrctl, v : xlenbits) -> Mctrctl = {
  let o = Mk_Mctrctl(zero_extend(v));
  let o = [o with M = m[M], MTE = m[MTE]];
  o
}


function get_wrptr_mask(d : Sctrdepth) -> bits(8) =
  match(d[DEPTH]) {
    0b000 => 0b00001111,  
    0b001 => 0b00011111,  
    0b010 => 0b00111111,  
    0b011 => 0b01111111,  
    0b100 => 0b11111111,  
        _ => internal_error(__FILE__, __LINE__, "Unexpected DEPTH encoding")
  }

function legalize_sctrdepth(s : Sctrdepth, v : xlenbits) -> Sctrdepth = {
  let valid_ctr_depth : bits(64) = sys_valid_ctr_depth();
  let depth : bits(3) = match(v[2 .. 0]) {
    0b000 => if bit_to_bool(valid_ctr_depth[0]) then v[2 .. 0] else s[DEPTH],
    0b001 => if bit_to_bool(valid_ctr_depth[1]) then v[2 .. 0] else s[DEPTH],
    0b010 => if bit_to_bool(valid_ctr_depth[2]) then v[2 .. 0] else s[DEPTH],
    0b011 => if bit_to_bool(valid_ctr_depth[3]) then v[2 .. 0] else s[DEPTH],
    0b100 => if bit_to_bool(valid_ctr_depth[4]) then v[2 .. 0] else s[DEPTH],
        _ => s[DEPTH]
  };
  let o = Mk_Sctrdepth(zero_extend(depth));

  /* On depth change WRPTR assumes an unspecified but legal value */
  sctrstatus[WRPTR] = sctrstatus[WRPTR] & get_wrptr_mask(o);

  o
}
function legalize_sctrstatus(s : Sctrstatus, v : xlenbits) -> Sctrstatus = {
  let wrptr_mask : bits(8) = get_wrptr_mask(sctrdepth);
  let o = Mk_Sctrstatus(zeros());
  let o = [o with WRPTR = (v[7 .. 0] & wrptr_mask), FROZEN = v[31 .. 31]];
  o
}
function number_of_ctr() -> int = {
  let valid_ctr_depth : bits(64) = sys_valid_ctr_depth();
  let num = if bit_to_bool(valid_ctr_depth[0]) then 16 else 0;
  let num = if bit_to_bool(valid_ctr_depth[1]) then 32 else num;
  let num = if bit_to_bool(valid_ctr_depth[2]) then 64 else num;
  let num = if bit_to_bool(valid_ctr_depth[3]) then 128 else num;
  let num = if bit_to_bool(valid_ctr_depth[4]) then 256 else num;
  num
}
function isValidCtrMiselect() -> bool = {
  let ctr_select = miselect.bits[7 .. 0];
  haveSmctr() & (unsigned(ctr_select) < number_of_ctr())
}
function isValidCtrSiselect() -> bool = {
  let ctr_select = siselect.bits[7 .. 0];
  haveSsctr() & (unsigned(ctr_select) < number_of_ctr())
}
/* Logical entry N, selected by *iselect value of (0x200 | N), is
 * physically at ((WRPTR - N - 1) % depth) where depth = 2^(DEPTH+4)
 */
function get_ctr_idx(iselect : SMiselect) -> bits(8) = {
  let ctr_idx = sctrstatus[WRPTR] - iselect.bits[7 .. 0] - 1;
  ctr_idx & get_wrptr_mask(sctrdepth);
}

function get_ctr_mireg() -> xlenbits =
  ctrsource[unsigned(get_ctr_idx(miselect))].bits

function get_ctr_mireg2() -> xlenbits =
  ctrtarget[unsigned(get_ctr_idx(miselect))].bits

function get_ctr_mireg3() -> xlenbits =
  ctrdata[unsigned(get_ctr_idx(miselect))].bits

function set_ctr_mireg(v: xlenbits) -> unit =
  ctrsource[unsigned(get_ctr_idx(miselect))] = Mk_Ctrsource(v)

function set_ctr_mireg2(v: xlenbits) -> unit =
  ctrtarget[unsigned(get_ctr_idx(miselect))] = Mk_Ctrtarget(v)

function set_ctr_mireg3(v: xlenbits) -> unit =
  ctrdata[unsigned(get_ctr_idx(miselect))] = Mk_Ctrdata(v)


function get_ctr_sireg() -> xlenbits =
  ctrsource[unsigned(get_ctr_idx(siselect))].bits

function get_ctr_sireg2() -> xlenbits =
  ctrsource[unsigned(get_ctr_idx(siselect))].bits

function get_ctr_sireg3() -> xlenbits =
  ctrsource[unsigned(get_ctr_idx(siselect))].bits

function set_ctr_sireg(v: xlenbits) -> unit =
  ctrsource[unsigned(get_ctr_idx(siselect))] = Mk_Ctrsource(v)

function set_ctr_sireg2(v: xlenbits) -> unit =
  ctrtarget[unsigned(get_ctr_idx(siselect))] = Mk_Ctrtarget(v)

function set_ctr_sireg3(v: xlenbits) -> unit =
  ctrdata[unsigned(get_ctr_idx(siselect))] = Mk_Ctrdata(v)
