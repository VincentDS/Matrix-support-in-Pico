/*-----------------------------------*/
/*             >>>Pico<<<            */
/*            Theo D'Hondt           */
/*   VUB Programming Technology Lab  */
/*             (c) 1997              */
/*-----------------------------------*/
/*            Evaluation             */
/*-----------------------------------*/

#include "Pico.h"
#include "PicoMai.h"
#include "PicoEnv.h"
#include "PicoMem.h"
#include "PicoNat.h"
#include "PicoEva.h"

/* private constants */

#define CAL _eval_CAL_   
#define EXP _eval_EXP_   
#define NAT _eval_NAT_   

/* private prototypes */

static _NIL_TYPE_ APL(_NIL_TYPE_);  
static _NIL_TYPE_ ASS(_NIL_TYPE_); 
static _NIL_TYPE_ ATA(_NIL_TYPE_); 
static _NIL_TYPE_ ATV(_NIL_TYPE_); 
static _NIL_TYPE_ BND(_NIL_TYPE_);
static _NIL_TYPE_ CHG(_NIL_TYPE_);
static _NIL_TYPE_ DEF(_NIL_TYPE_); 
static _NIL_TYPE_ IDX(_NIL_TYPE_); 
static _NIL_TYPE_ INI(_NIL_TYPE_); 
static _NIL_TYPE_ NYI(_NIL_TYPE_); 
static _NIL_TYPE_ REF(_NIL_TYPE_); 
static _NIL_TYPE_ RET(_NIL_TYPE_); 
static _NIL_TYPE_ RPL(_NIL_TYPE_); 
static _NIL_TYPE_ SET(_NIL_TYPE_); 
static _NIL_TYPE_ SLF(_NIL_TYPE_); 
static _NIL_TYPE_ SWP(_NIL_TYPE_); 
static _NIL_TYPE_ TBL(_NIL_TYPE_); 
static _NIL_TYPE_ VAR(_NIL_TYPE_);
static _NIL_TYPE_ DIM(_NIL_TYPE_);
static _NIL_TYPE_ MDX(_NIL_TYPE_);
static _NIL_TYPE_ MNI(_NIL_TYPE_);
static _NIL_TYPE_ MTX(_NIL_TYPE_);
static _NIL_TYPE_ IXM(_NIL_TYPE_);
static _NIL_TYPE_ MWP(_NIL_TYPE_);
static _NIL_TYPE_ MPL(_NIL_TYPE_);
static _NIL_TYPE_ MEF(_NIL_TYPE_);


/* private variables */ 

static const _BYT_TYPE_ TAB_tab[] =
   { 0,    /* VOI */
     1,    /* NAT */ 
     0,    /* FRC */
     0,    /* TXT */
     1,    /* TAB */
     1,    /* FUN */
     1,    /* VAR */
     1,    /* APL */
     1,    /* TBL */
     1,    /* DEF */
     1,    /* SET */
     1,    /* DCT */
     1,    /* ENV */
     1,    /* MTX */
     0,    /* NYI */
     0,    /* NYI */
     0 };  /* NBR */
     
static const _CNT_TYPE_ CNT_tab[] = 
   { SLF,    /* VOI */
     SLF,    /* NAT */ 
     SLF,    /* FRC */
     SLF,    /* TXT */
     SLF,    /* TAB */
     SLF,    /* FUN */
     VAR,    /* VAR */
     APL,    /* APL */
     TBL,    /* TBL */
     DEF,    /* DEF */
     SET,    /* SET */
     SLF,    /* DCT */
     SLF,    /* ENV */
     DIM,    /* DIM */
     MTX,    /* MTX */
     NYI,    /* NYI */
     SLF };  /* NBR */
 
/* private functions */

/*------------------------------------------------------------------------*/
/*  NYI                                                                   */
/*     expr-stack: [... ... ... ... ... EXP] -> [... ... ... ... ... ...] */
/*     cont-stack: [... ... ... ... ... NYI] -> [... ... ... ... ... ERR] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ NYI(_NIL_TYPE_)
 { _error_(_AGR_ERROR_); }
   
/*------------------------------------------------------------------------*/
/*  APL                                                                   */
/*     expr-stack: [... ... ... ... ... APL] -> [... ... ... ... FUN ARG] */
/*     cont-stack: [... ... ... ... ... APL] -> [... ... ... ... ... CAL] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... APL] -> [... ... ... ... FUN ARG] */
/*     cont-stack: [... ... ... ... ... APL] -> [... ... ... ... CAL EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... APL] -> [... ... ... ... NBR ARG] */
/*     cont-stack: [... ... ... ... ... APL] -> [... ... ... ... ... NAT] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... APL] -> [... ... ... ... NBR ARG] */
/*     cont-stack: [... ... ... ... ... APL] -> [... ... ... ... NAT EXP] */
/*------------------------------------------------------------------------*/

static _NIL_TYPE_ APL(_NIL_TYPE_)
 { _EXP_TYPE_ apl, arg, dct, fun, nam, nbr;
   _TAG_TYPE_ tag;
   _stk_claim_();
   _stk_peek_EXP_(apl);
   nam = _ag_get_APL_NAM_(apl);
   arg = _ag_get_APL_ARG_(apl);
   _dct_locate_(nam, dct, _DCT_);
   fun = _ag_get_DCT_VAL_(dct);
   tag = _ag_get_TAG_(fun);
   switch (tag)
    { case _FUN_TAG_:
        _stk_poke_EXP_(fun);
        _stk_poke_CNT_(CAL);
        break;
      case _NAT_TAG_:
        nbr = _ag_get_NAT_NBR_(fun);
        _stk_poke_EXP_(nbr);
        _stk_poke_CNT_(NAT);
        break; 
      default:
        _error_msg_(_NAF_ERROR_, nam); }
   _stk_push_EXP_(arg);
   tag = _ag_get_TAG_(arg);
   if (tag != _TAB_TAG_)  
     _stk_push_CNT_(EXP); }

/*------------------------------------------------------------------------*/
/*  ASS                                                                   */
/*     expr-stack: [... ... ... ... DCT VAL] -> [... ... ... ... ... VAL] */
/*     cont-stack: [... ... ... ... ... ASS] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ ASS(_NIL_TYPE_)
 { _EXP_TYPE_ dct, val;
   _stk_pop_EXP_(val);
   _stk_peek_EXP_(dct);
   _ag_set_DCT_VAL_(dct, val);
   _ag_set_DCT_DCT_(dct, _DCT_);
   _DCT_ = dct; 
   _stk_poke_EXP_(val); 
   _stk_zap_CNT_(); }

/*------------------------------------------------------------------------*/
/*  ATA                                                                   */
/*     expr-stack: [EXP DCT ARG TAB NBR APL] -> [EXP DCT ARG TAB NBR APL] */
/*     cont-stack: [... ... ... ... ... ATA] -> [... ... ... ... ... ATA] */
/*                                                                        */
/*     expr-stack: [EXP DCT ARG TAB NBR APL] -> [... ... ... ... DCT EXP] */
/*     cont-stack: [... ... ... ... ... ATA] -> [... ... ... ... RET EXP] */
/*                                                                        */
/*     expr-stack: [EXP DCT ARG TAB NBR APL] -> [... ... ... ... ... EXP] */
/*     cont-stack: [... ... ... ... ... ATA] -> [... ... ... ... ... EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ ATA(_NIL_TYPE_)
 { _EXP_TYPE_ act, apl, arg, dct, exp, fun, nam, nbr, par, tab;
   _CNT_TYPE_ cnt;
   _UNS_TYPE_ ctr, siz;
   _mem_claim_();
   fun = _ag_make_FUN_();
   _stk_pop_EXP_(apl);
   _stk_pop_EXP_(nbr);
   _stk_pop_EXP_(tab);
   _stk_pop_EXP_(arg);
   _stk_peek_EXP_(dct);
   siz = _ag_get_TAB_SIZ_(arg);
   ctr = _ag_get_NBU_(nbr);
   act = _ag_get_TAB_EXP_(arg, ctr);
   nam = _ag_get_APL_NAM_(apl);
   par = _ag_get_APL_ARG_(apl);
   _ag_set_FUN_NAM_(fun, nam);
   _ag_set_FUN_ARG_(fun, par);
   _ag_set_FUN_EXP_(fun, act);
   // _ag_set_FUN_DCT_(fun, dct);
   _ag_set_FUN_DCT_(fun, _DCT_); // jdk
   _ag_set_TAB_EXP_(tab, ctr, fun);
   if (ctr < siz)
     { _stk_push_EXP_(arg);
       _stk_push_EXP_(tab);
       nbr = _ag_succ_NBR_(nbr);
       _stk_push_EXP_(nbr);
       _stk_push_EXP_(apl); }
   else
     { _ag_set_DCT_VAL_(dct, tab);
       _stk_zap_EXP_();
       _stk_zap_CNT_();
       _stk_peek_CNT_(cnt);
       if (cnt != RET)
         { _stk_peek_EXP_(exp);
           _stk_poke_EXP_(_DCT_);
           _stk_push_EXP_(exp); 
           _stk_push_CNT_(RET); }
       _stk_push_CNT_(EXP); 
       _DCT_ = dct; }}

/*------------------------------------------------------------------------*/
/*  ATV                                                                   */
/*     expr-stack: [EXP DCT ARG TAB NBR VAL] -> [EXP DCT ARG TAB NBR EXP] */
/*     cont-stack: [... ... ... ... ... ATV] -> [... ... ... ... ATV EXP] */
/*                                                                        */
/*     expr-stack: [EXP DCT ARG TAB NBR VAL] -> [... ... ... ... DCT EXP] */
/*     cont-stack: [... ... ... ... ... ATV] -> [... ... ... ... RET EXP] */
/*                                                                        */
/*     expr-stack: [EXP DCT ARG TAB NBR VAL] -> [... ... ... ... ... EXP] */
/*     cont-stack: [... ... ... ... ... ATV] -> [... ... ... ... ... EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ ATV(_NIL_TYPE_)
 { _EXP_TYPE_ act, arg, dct, exp, nbr, tab, val;
   _CNT_TYPE_ cnt;
   _UNS_TYPE_ ctr, siz;
   _stk_claim_();
   _stk_pop_EXP_(val);
   _stk_pop_EXP_(nbr);
   _stk_pop_EXP_(tab);
   _stk_peek_EXP_(arg);
   siz = _ag_get_TAB_SIZ_(arg);
   ctr = _ag_get_NBU_(nbr);
   _ag_set_TAB_EXP_(tab, ctr, val);
   if (ctr < siz)
     { act = _ag_get_TAB_EXP_(arg, ctr+1);
       _stk_push_EXP_(tab);
       nbr = _ag_succ_NBR_(nbr);
       _stk_push_EXP_(nbr);
       _stk_push_EXP_(act);
       _stk_push_CNT_(EXP); }
   else
     { _stk_zap_EXP_();
       _stk_pop_EXP_(dct);
       _ag_set_DCT_VAL_(dct, tab);
       _stk_zap_CNT_();
       _stk_peek_CNT_(cnt);
       if (cnt != RET)
         { _stk_peek_EXP_(exp);
           _stk_poke_EXP_(_DCT_);
           _stk_push_EXP_(exp); 
           _stk_push_CNT_(RET); }
       _stk_push_CNT_(EXP); 
       _DCT_ = dct; }}

/*------------------------------------------------------------------------*/
/*  BND                                                                   */
/*     expr-stack: [EXP PAR ARG NBR DCT VAL] -> [... ... ... ... DCT EXP] */
/*     cont-stack: [... ... ... ... ... BND] -> [... ... ... ... RET EXP] */
/*                                                                        */
/*     expr-stack: [EXP PAR ARG NBR DCT VAL] -> [... ... ... ... ... EXP] */
/*     cont-stack: [... ... ... ... ... BND] -> [... ... ... ... ... EXP] */
/*                                                                        */
/*     expr-stack: [EXP PAR ARG NBR DCT VAL] -> [EXP PAR ARG NBR DCT EXP] */
/*     cont-stack: [... ... ... ... ... BND] -> [... ... ... ... BND EXP] */
/*                                                                        */
/*     expr-stack: [EXP PAR ARG NBR DCT VAL] -> [EXP PAR ARG NBR DCT FUN] */
/*     cont-stack: [... ... ... ... ... BND] -> [... ... ... ... ... BND] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ BND(_NIL_TYPE_)
 { _EXP_TYPE_ act, arg, dct, exp, fun, frm, nam, nbr, par, val, xdc;
   _CNT_TYPE_ cnt;
   _TAG_TYPE_ tag;
   _UNS_TYPE_ ctr, siz;
   _stk_claim_();
   _mem_claim_();
   _stk_pop_EXP_(val);
   _stk_pop_EXP_(dct);
   _ag_set_DCT_VAL_(dct, val);
   _stk_pop_EXP_(nbr);
   _stk_pop_EXP_(arg);
   siz = _ag_get_TAB_SIZ_(arg);
   ctr = _ag_get_NBU_(nbr);
   if (ctr == siz)
     { _stk_zap_EXP_();
       _stk_zap_CNT_();
       _stk_peek_CNT_(cnt);
       if (cnt != RET)
         { _stk_peek_EXP_(exp);
           _stk_poke_EXP_(_DCT_);
           _stk_push_EXP_(exp); 
           _stk_push_CNT_(RET); }
       _stk_push_CNT_(EXP); 
       _DCT_ = dct; }
   else
     { _stk_peek_EXP_(par);
       frm = _ag_get_TAB_EXP_(par, ++ctr);
       act = _ag_get_TAB_EXP_(arg, ctr);
       tag = _ag_get_TAG_(frm);
       _stk_push_EXP_(arg); 
       nbr = _ag_succ_NBR_(nbr);
       _stk_push_EXP_(nbr); 
       xdc = _ag_make_DCT_();
       _stk_push_EXP_(xdc); 
       _ag_set_DCT_DCT_(xdc, dct);
       switch (tag)
        { case _VAR_TAG_:          
            nam = _ag_get_VAR_NAM_(frm);    
            _ag_set_DCT_NAM_(xdc, nam);
            _stk_push_EXP_(act);
            _stk_push_CNT_(EXP);
            break;
          case _APL_TAG_:
            fun = _ag_make_FUN_();
            nam = _ag_get_APL_NAM_(frm);
            arg = _ag_get_APL_ARG_(frm);
            _ag_set_DCT_NAM_(xdc, nam);
            _ag_set_FUN_NAM_(fun, nam);
            _ag_set_FUN_ARG_(fun, arg);
            _ag_set_FUN_EXP_(fun, act);
            _ag_set_FUN_DCT_(fun, _DCT_);
            _stk_push_EXP_(fun);
             break;
          default:
            _error_(_IPM_ERROR_); }}}
   
/*------------------------------------------------------------------------*/
/*  CHG                                                                   */
/*     expr-stack: [... ... ... ... DCT VAL] -> [... ... ... ... ... VAL] */
/*     cont-stack: [... ... ... ... ... CHG] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ CHG(_NIL_TYPE_)
 { _EXP_TYPE_ dct, val;
   _stk_pop_EXP_(val);
   _stk_peek_EXP_(dct);
   _ag_set_DCT_VAL_(dct, val);
   _stk_poke_EXP_(val); 
   _stk_zap_CNT_(); }

/*------------------------------------------------------------------------*/
/*  DEF                                                                   */
/*     expr-stack: [... ... ... ... ... DEF] -> [... ... ... ... DCT EXP] */
/*     cont-stack: [... ... ... ... ... DEF] -> [... ... ... ... ASS EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... DEF] -> [... ... ... ... ... FUN] */
/*     cont-stack: [... ... ... ... ... DEF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... DEF] -> [... ... ... DCT EXP IDX] */
/*     cont-stack: [... ... ... ... ... DEF] -> [... ... ... ... IDX EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... DEF] -> [DCT EXP TAB SIZ *1* EXP] */
/*     cont-stack: [... ... ... ... ... DEF] -> [... ... ... MDX DIM EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ DEF(_NIL_TYPE_)
 { _EXP_TYPE_ arg, dct, def, exp, fun, idx, inv, nam, dim, siz;
   _TAG_TYPE_ tag;
   _stk_claim_();
   _mem_claim_();
   dct = _ag_make_DCT_();
   _stk_peek_EXP_(def);
   inv = _ag_get_DEF_INV_(def);
   exp = _ag_get_DEF_EXP_(def);
   tag = _ag_get_TAG_(inv);
   switch (tag)
    { case _VAR_TAG_:
        nam = _ag_get_VAR_NAM_(inv);
        _ag_set_DCT_NAM_(dct, nam);
        _stk_poke_EXP_(dct);
        _stk_push_EXP_(exp);
        _stk_poke_CNT_(ASS);
        _stk_push_CNT_(EXP); 
        break;
      case _APL_TAG_:
        fun = _ag_make_FUN_();
        nam = _ag_get_APL_NAM_(inv);
        arg = _ag_get_APL_ARG_(inv);
        _ag_set_DCT_NAM_(dct, nam);
        _ag_set_DCT_VAL_(dct, fun);
			  _ag_set_DCT_DCT_(dct, _DCT_);
			  _DCT_ = dct; 
        _ag_set_FUN_NAM_(fun, nam);
        _ag_set_FUN_ARG_(fun, arg);
        _ag_set_FUN_EXP_(fun, exp);
        _ag_set_FUN_DCT_(fun, dct);
        _stk_poke_EXP_(fun); 
        _stk_zap_CNT_(); 
        break;
      case _TBL_TAG_:
        nam = _ag_get_TBL_NAM_(inv);
        idx = _ag_get_TBL_IDX_(inv);
        _ag_set_DCT_NAM_(dct, nam);
        _stk_poke_EXP_(dct);
        _stk_push_EXP_(exp);
        _stk_push_EXP_(idx);
        _stk_poke_CNT_(IDX);
        _stk_push_CNT_(EXP); 
        break;
      case _MTX_TAG_:
        nam = _ag_get_MTX_NAM_(inv);
        dim = _ag_get_MTX_DIM_(inv);
        _ag_set_DCT_NAM_(dct, nam);
        siz = _ag_make_NBU_(1); //neutral element for multiplication
        idx = _ag_get_TAB_EXP_(dim, 1);
        _stk_poke_EXP_(dct);
        _stk_push_EXP_(exp);
        _stk_push_EXP_(dim);
        _stk_push_EXP_(siz);
        _stk_push_EXP_(_ONE_);
        _stk_push_EXP_(idx); //all the expressions in the dim-table needs to be evaluated
        _stk_poke_CNT_(MDX);
        _stk_push_CNT_(DIM);
        _stk_push_CNT_(EXP);
        break;
      default:
        _error_(_AGR_ERROR_); }}

/*
 calculates the total size of the matrix
 */
/*------------------------------------------------------------------------*/
/*  DIM                                                                   */
/*     expr-stack: [DCT EXP TAB SIZ NBR VAL] -> [DCT EXP TAB SIZ NBR EXP] */ //recursion to calculate the size of the table
/*     cont-stack: [... ... ... ... MDX DIM] -> [... ... ... MDX DIM EXP] */
/*                                                                        */
/*     expr-stack: [DCT EXP TAB SIZ NBR VAL] -> [... ... DCT MAT EXP NBR] */ //NBR is now the size of the table
/*     cont-stack: [... ... ... ... MDX DIM] -> [... ... ... ... ... MDX] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ DIM(_NIL_TYPE_)
{ _EXP_TYPE_  exp, val, siz, dim, ctr, mat;
  _UNS_TYPE_ ctr_val, siz_val, val_val, dim_siz_val;
  _stk_claim_();
  _mem_claim_();
  _stk_pop_EXP_(val);
  _stk_pop_EXP_(ctr);
  _stk_pop_EXP_(siz);
  _stk_peek_EXP_(dim);
  ctr_val = _ag_get_NBU_(ctr);
  siz_val = _ag_get_NBU_(siz);
  val_val = _ag_get_NBU_(val);
  siz_val *= val_val;
  siz = _ag_make_NBU_(siz_val);
  dim_siz_val = _ag_get_TAB_SIZ_(dim);
  _ag_set_TAB_EXP_(dim, ctr_val, val);
  if (ctr_val < dim_siz_val) { //not at the end of the dimensions-table
      ctr = _ag_succ_NBR_(ctr); //increment counter
      ctr_val += 1;
      exp = _ag_get_TAB_EXP_(dim, ctr_val); //take the next expression out of the table
      _stk_push_EXP_(siz);
      _stk_push_EXP_(ctr);
      _stk_push_EXP_(exp);
      _stk_push_CNT_(EXP);
  } else {
      _stk_pop_EXP_(dim);
      _stk_pop_EXP_(exp);
      mat = _ag_make_MAT_();
      _ag_set_MAT_DIM_(mat, dim); //fills in the dimension of the matrix
      _stk_push_EXP_(mat);
      _stk_push_EXP_(exp);
      _stk_push_EXP_(siz);
      _stk_zap_CNT_();
	}
    
}
/*
 same as IDX but for matrices. Starts the loop that fills in exp in the matrix
 */
/*------------------------------------------------------------------------*/
/*  MDX                                                                   */
/*     expr-stack: [... ... DCT MAT EXP NBR] -> [DCT MAT TAB EXP *1* EXP] */
/*     cont-stack: [... ... ... ... ... MDX] -> [... ... ... ... MNI EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ MDX(_NIL_TYPE_)
{ _EXP_TYPE_ exp, nbr, tab;
    _TAG_TYPE_ tag;
    _UNS_TYPE_ siz;
    _stk_claim_(); //because we enlarge our stacks
    _stk_pop_EXP_(nbr);
    tag = _ag_get_TAG_(nbr);
    siz = _ag_get_NBU_(nbr);
    if (tag == _NBR_TAG_)
    { _mem_claim_SIZ_(siz); //because we make a tab en we surely need enough memory
      tab = _ag_make_TAB_(siz);
      _stk_peek_EXP_(exp);
      _stk_poke_EXP_(tab);
      _stk_push_EXP_(exp);
      _stk_push_EXP_(_ONE_);
      _stk_push_EXP_(exp);
      _stk_poke_CNT_(MNI);
      _stk_push_CNT_(EXP); }
    else
        _error_(_SIZ_ERROR_); }

/*
 same as INI but for matrices
 */
/*------------------------------------------------------------------------*/
/*  MNI                                                                   */
/*     expr-stack: [DCT MAT TAB EXP NBR VAL] -> [DCT MAT TAB EXP NBR EXP] */
/*     cont-stack: [... ... ... ... ... MNI] -> [... ... ... ... MNI EXP] */
/*                                                                        */
/*     expr-stack: [DCT MAT TAB EXP NBR VAL] -> [... ... ... ... ... MAT] */
/*     cont-stack: [... ... ... ... ... MNI] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ MNI(_NIL_TYPE_)
{ _EXP_TYPE_ dct, exp, nbr, tab, val, mat;
    _UNS_TYPE_ ctr, siz;
    _stk_claim_();
    _stk_pop_EXP_(val);
    _stk_pop_EXP_(nbr);
    _stk_pop_EXP_(exp);
    _stk_peek_EXP_(tab);
    siz = _ag_get_TAB_SIZ_(tab);
    ctr = _ag_get_NBU_(nbr);
    _ag_set_TAB_EXP_(tab, ctr, val);
    if (ctr < siz)
    { nbr = _ag_succ_NBR_(nbr);
        _stk_push_EXP_(exp);
        _stk_push_EXP_(nbr);
        _stk_push_EXP_(exp);
        _stk_push_CNT_(EXP); }
    else
    { _stk_zap_EXP_();
        _stk_pop_EXP_(mat);
        _stk_peek_EXP_(dct);
        _ag_set_MAT_TAB_(mat, tab);
        _ag_set_DCT_VAL_(dct, mat);
        _ag_set_DCT_DCT_(dct, _DCT_);
        _DCT_ = dct;
        _stk_poke_EXP_(mat);
        _stk_zap_CNT_(); }}

/*------------------------------------------------------------------------*/
/*  IDX                                                                   */
/*     expr-stack: [... ... ... DCT EXP NBR] -> [... DCT TAB EXP *1* EXP] */
/*     cont-stack: [... ... ... ... ... IDX] -> [... ... ... ... INI EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... DCT EXP NBR] -> [... ... ... ... ... *E*] */
/*     cont-stack: [... ... ... ... ... IDX] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ IDX(_NIL_TYPE_)
 { _EXP_TYPE_ dct, exp, nbr, tab;
   _TAG_TYPE_ tag;
   _UNS_TYPE_ siz;
   _stk_claim_();
   _stk_pop_EXP_(nbr);
   tag = _ag_get_TAG_(nbr);
   if (tag == _NBR_TAG_) 
     { siz = _ag_get_NBU_(nbr);
       if (siz == 0) 
         { _stk_zap_EXP_();
           _stk_peek_EXP_(dct);
           _ag_set_DCT_VAL_(dct, _EMPTY_); 
				   _ag_set_DCT_DCT_(dct, _DCT_);
				   _DCT_ = dct; 
           _stk_poke_EXP_(_EMPTY_);
           _stk_zap_CNT_(); }
       else if (siz > 0)
         { _mem_claim_SIZ_(siz);
           tab = _ag_make_TAB_(siz);
           _stk_peek_EXP_(exp);
           _stk_poke_EXP_(tab);
           _stk_push_EXP_(exp);
           _stk_push_EXP_(_ONE_);
           _stk_push_EXP_(exp);
           _stk_poke_CNT_(INI);
           _stk_push_CNT_(EXP); }
	     else
	       _error_(_SIZ_ERROR_);}
   else
     _error_(_SIZ_ERROR_); }

/*------------------------------------------------------------------------*/
/*  INI                                                                   */
/*     expr-stack: [... DCT TAB EXP NBR VAL] -> [... DCT TAB EXP NBR EXP] */
/*     cont-stack: [... ... ... ... ... INI] -> [... ... ... ... INI EXP] */
/*                                                                        */
/*     expr-stack: [... DCT TAB EXP NBR VAL] -> [... ... ... ... ... TAB] */
/*     cont-stack: [... ... ... ... ... INI] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ INI(_NIL_TYPE_)
{ _EXP_TYPE_ dct, exp, nbr, tab, val;
    _UNS_TYPE_ ctr, siz;
    _stk_claim_();
    _stk_pop_EXP_(val);
    _stk_pop_EXP_(nbr);
    _stk_pop_EXP_(exp);
    _stk_peek_EXP_(tab);
    siz = _ag_get_TAB_SIZ_(tab);
    ctr = _ag_get_NBU_(nbr);
    _ag_set_TAB_EXP_(tab, ctr, val);
    if (ctr < siz)
    { nbr = _ag_succ_NBR_(nbr);
        _stk_push_EXP_(exp);
        _stk_push_EXP_(nbr);
        _stk_push_EXP_(exp);
        _stk_push_CNT_(EXP); }
    else
    { _stk_zap_EXP_();
        _stk_peek_EXP_(dct);
        _ag_set_DCT_VAL_(dct, tab);
        _ag_set_DCT_DCT_(dct, _DCT_);
        _DCT_ = dct;
        _stk_poke_EXP_(tab);
        _stk_zap_CNT_(); }}

  
/*------------------------------------------------------------------------*/
/*  REF                                                                   */
/*     expr-stack: [... ... ... ... TAB NBR] -> [... ... ... ... ... VAL] */
/*     cont-stack: [... ... ... ... ... REF] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ REF(_NIL_TYPE_)
 { _EXP_TYPE_ exp, nbr, tab;
   _UNS_TYPE_ ctr, siz;
   _TAG_TYPE_ tag;
   _stk_pop_EXP_(nbr);
   _stk_peek_EXP_(tab);
   tag = _ag_get_TAG_(tab);
   if (TAB_tab[tag])
     { siz = _ag_get_TAB_SIZ_(tab);
       tag = _ag_get_TAG_(nbr);
       if (tag == _NBR_TAG_) 
         { ctr = _ag_get_NBU_(nbr);
           if ((ctr > 0) && (ctr <= siz))
             { exp = _ag_get_TAB_EXP_(tab, ctr);
               _stk_poke_EXP_(exp);
               _stk_zap_CNT_(); }
           else
             _error_(_RNG_ERROR_); }
       else
        _error_(_IIX_ERROR_); }
   else 
     _error_(_NAT_ERROR_); }

/*
 Same as REF but for matrices
 */
/*------------------------------------------------------------------------*/
/*  MEF                                                                   */
/*     expr-stack: [... ... ... ... MAT NBR] -> [... ... ... ... ... VAL] */
/*     cont-stack: [... ... ... ... ... REF] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ MEF(_NIL_TYPE_)
{ _EXP_TYPE_ exp, nbr, tab, mat;
    _UNS_TYPE_ ctr, siz;
    _TAG_TYPE_ tag;
    _stk_pop_EXP_(nbr);
    _stk_peek_EXP_(mat);
    tab = _ag_get_MAT_TAB_(mat);
    tag = _ag_get_TAG_(tab);
    if (TAB_tab[tag])
    { siz = _ag_get_TAB_SIZ_(tab);
        tag = _ag_get_TAG_(nbr);
        if (tag == _NBR_TAG_)
        { ctr = _ag_get_NBU_(nbr);
            if ((ctr > 0) && (ctr <= siz))
            { exp = _ag_get_TAB_EXP_(tab, ctr);
                _stk_poke_EXP_(exp);
                _stk_zap_CNT_(); }
            else
                _error_(_RNG_ERROR_); }
        else
            _error_(_IIX_ERROR_); }
    else
        _error_(_NAT_ERROR_); }

/*------------------------------------------------------------------------*/
/*  RET                                                                   */
/*     expr-stack: [... ... ... ... DCT VAL] -> [... ... ... ... ... VAL] */
/*     cont-stack: [... ... ... ... ... RET] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ RET(_NIL_TYPE_)
 { _EXP_TYPE_ val;
   _stk_pop_EXP_(val);
   _stk_peek_EXP_(_DCT_);
   _stk_poke_EXP_(val);
   _stk_zap_CNT_(); 
   _ESCAPE_; }

/*------------------------------------------------------------------------*/
/*  RPL                                                                   */
/*     expr-stack: [... ... ... TAB VAL NBR] -> [... ... ... ... ... TAB] */
/*     cont-stack: [... ... ... ... ... RPL] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ RPL(_NIL_TYPE_)
 { _EXP_TYPE_ nbr, tab, val;
   _UNS_TYPE_ ctr, siz;
   _TAG_TYPE_ tag;
   _stk_pop_EXP_(nbr);
   _stk_pop_EXP_(val);
   _stk_peek_EXP_(tab);
   tag = _ag_get_TAG_(tab);
   if (TAB_tab[tag])
     { siz = _ag_get_TAB_SIZ_(tab);
       tag = _ag_get_TAG_(nbr);
       if (tag == _NBR_TAG_) 
         { ctr = _ag_get_NBU_(nbr);
           if ((ctr > 0) && (ctr <= siz))
             { _ag_set_TAB_EXP_(tab, ctr, val);
               _stk_zap_CNT_(); }
           else
             _error_(_RNG_ERROR_); }
       else
         _error_(_IIX_ERROR_); }
   else 
     _error_(_NAT_ERROR_); }

/*
 assigns the val to the matrix at index NBR. looks like RPL but for matrices
 */
/*------------------------------------------------------------------------*/
/*  MPL                                                                   */
/*     expr-stack: [... ... ... MAT NBR VAL] -> [... ... ... ... ... MAT] */
/*     cont-stack: [... ... ... ... ... MPL] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ MPL(_NIL_TYPE_)
{ _EXP_TYPE_ nbr, mat, val, tab;
    _UNS_TYPE_ ctr, siz;
    _TAG_TYPE_ tag;
    _stk_pop_EXP_(val);
    _stk_pop_EXP_(nbr);
    _stk_peek_EXP_(mat);
    tab = _ag_get_MAT_TAB_(mat);
    tag = _ag_get_TAG_(tab);
    if (TAB_tab[tag])
    { siz = _ag_get_TAB_SIZ_(tab);
        tag = _ag_get_TAG_(nbr);
        if (tag == _NBR_TAG_)
        { ctr = _ag_get_NBU_(nbr);
            if ((ctr > 0) && (ctr <= siz))
            { _ag_set_TAB_EXP_(tab, ctr, val);
                _stk_zap_CNT_(); }
            else
                _error_(_RNG_ERROR_); }
        else
            _error_(_IIX_ERROR_); }
    else
        _error_(_NAT_ERROR_); }


/*--------------------------------------------------------------------------------*/
/*  SET                                                                           */
/*     expr-stack: [... ... ... ... ... SET] -> [... ... ... ... ... ... DCT EXP] */
/*     cont-stack: [... ... ... ... ... SET] -> [... ... ... ... ... ... CHG EXP] */
/*                                                                                */
/*     expr-stack: [... ... ... ... ... SET] -> [... ... ... ... ... ... ... FUN] */
/*     cont-stack: [... ... ... ... ... SET] -> [... ... ... ... ... ... ... ...] */
/*                                                                                */
/*     expr-stack: [... ... ... ... ... SET] -> [... ... ... ... ... TAB IDX EXP] */
/*     cont-stack: [... ... ... ... ... SET] -> [... ... ... ... ... RPL SWP EXP] */
/*                                                                                */
/*     expr-stack: [... ... ... ... ... SET] -> [EXP MAT *0* DIM TAB *1* NBR EXP] */
/*     cont-stack: [... ... ... ... ... SET] -> [... ... ... ... RPL MWP IXM EXP] */
/*--------------------------------------------------------------------------------*/
static _NIL_TYPE_ SET(_NIL_TYPE_)
 { _EXP_TYPE_ arg, dct, exp, fun, idx, inv, nam, set, tab, dim, siz, mat, dat;
   _UNS_TYPE_ tab_siz, dim_siz;
   _TAG_TYPE_ tag;
   _stk_claim_();
   _mem_claim_();
   _stk_peek_EXP_(set);
   inv = _ag_get_SET_INV_(set);
   exp = _ag_get_SET_EXP_(set);
   tag = _ag_get_TAG_(inv);
   switch (tag)
    { case _VAR_TAG_:
        nam = _ag_get_VAR_NAM_(inv);
        _dct_locate_(nam, dct, _DCT_);
        _stk_poke_EXP_(dct);
        _stk_push_EXP_(exp);
        _stk_poke_CNT_(CHG);
        _stk_push_CNT_(EXP); 
        break;
      case _APL_TAG_:
        fun = _ag_make_FUN_();
        inv = _ag_get_SET_INV_(set);
        nam = _ag_get_APL_NAM_(inv);
        arg = _ag_get_APL_ARG_(inv);
        _dct_locate_(nam, dct, _DCT_);
        _ag_set_DCT_VAL_(dct, fun);
        _ag_set_FUN_NAM_(fun, nam);
        _ag_set_FUN_ARG_(fun, arg);
        _ag_set_FUN_EXP_(fun, exp);
        _ag_set_FUN_DCT_(fun, _DCT_);
        _stk_poke_EXP_(fun); 
        _stk_zap_CNT_(); 
        break;
      case _TBL_TAG_:
        nam = _ag_get_TBL_NAM_(inv);
        idx = _ag_get_TBL_IDX_(inv);
        _dct_locate_(nam, dct, _DCT_);
        tab = _ag_get_DCT_VAL_(dct);
        _stk_poke_EXP_(tab);
        _stk_push_EXP_(idx);
        _stk_push_EXP_(exp);
        _stk_poke_CNT_(RPL);
        _stk_push_CNT_(SWP);    
        _stk_push_CNT_(EXP); 
        break;
      case _MTX_TAG_:
        nam = _ag_get_MTX_NAM_(inv);
        tab = _ag_get_MTX_DIM_(inv);
        _dct_locate_(nam, dct, _DCT_);
        mat = _ag_get_DCT_VAL_(dct);
        dim = _ag_get_MAT_DIM_(mat);
        dat = _ag_get_MAT_TAB_(mat);
        tab_siz = _ag_get_TAB_SIZ_(tab);
        dim_siz = _ag_get_TAB_SIZ_(dim);
        if (tab_siz == dim_siz)
        { siz = _ag_make_NBU_(tab_siz);
            _stk_poke_EXP_(exp);
            _stk_push_EXP_(mat);
            _stk_push_EXP_(_ZERO_);
            _stk_push_EXP_(dim);
            _stk_push_EXP_(tab);
            _stk_push_EXP_(_ONE_);
            _stk_push_EXP_(siz);
            _stk_push_EXP_(_ag_get_TAB_EXP_(tab, tab_siz));
            _stk_poke_CNT_(MPL);
            _stk_push_CNT_(MWP);
            _stk_push_CNT_(IXM);
            _stk_push_CNT_(EXP);
        } else {
            _error_(_NMA_ERROR_);}
        break;
      default:
       _error_(_AGR_ERROR_); }}
        
/*------------------------------------------------------------------------*/
/*  SLF                                                                   */
/*     expr-stack: [... ... ... ... ... VOI] -> [... ... ... ... ... VOI] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... NAT] -> [... ... ... ... ... NAT] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... FRC] -> [... ... ... ... ... FRC] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... TXT] -> [... ... ... ... ... TXT] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... TAB] -> [... ... ... ... ... TAB] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... FUN] -> [... ... ... ... ... FUN] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... DCT] -> [... ... ... ... ... DCT] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... ENV] -> [... ... ... ... ... ENV] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*     expr-stack: [... ... ... ... ... NBR] -> [... ... ... ... ... NBR] */
/*     cont-stack: [... ... ... ... ... SLF] -> [... ... ... ... ... ...] */
/*                                                                        */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ SLF(_NIL_TYPE_)
 { _stk_zap_CNT_(); }
   
/*------------------------------------------------------------------------*/
/*  SWP                                                                   */
/*     expr-stack: [... ... ... TAB EXP VAL] -> [... ... ... TAB VAL EXP] */
/*     cont-stack: [... ... ... ... ... SWP] -> [... ... ... ... ... EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ SWP(_NIL_TYPE_)
 { _EXP_TYPE_ exp, val; 
   _stk_pop_EXP_(val);
   _stk_peek_EXP_(exp);
   _stk_poke_EXP_(val);
   _stk_push_EXP_(exp);  
   _stk_poke_CNT_(EXP); }

/*
 swaps the data so we can evaluate the expression that needs to be put in the table by MPL
 */
/*------------------------------------------------------------------------*/
/*  MWP                                                                   */
/*     expr-stack: [... ... ... EXP MAT NBR] -> [... ... ... MAT NBR EXP] */
/*     cont-stack: [... ... ... ... MPL MWP] -> [... ... ... ... MPL EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ MWP(_NIL_TYPE_)
{ _EXP_TYPE_ exp, nbr, mat;
    _stk_pop_EXP_(nbr); //index in the tab
    _stk_pop_EXP_(mat);
    _stk_peek_EXP_(exp);
    _stk_poke_EXP_(mat);
    _stk_push_EXP_(nbr);
    _stk_push_EXP_(exp);
    _stk_poke_CNT_(EXP); }

/*------------------------------------------------------------------------*/
/*  TBL                                                                   */
/*     expr-stack: [... ... ... ... ... TBL] -> [... ... ... ... TAB EXP] */
/*     cont-stack: [... ... ... ... ... TBL] -> [... ... ... ... REF EXP] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ TBL(_NIL_TYPE_)
 { _EXP_TYPE_ dct, idx, nam, tab, tbl;
   _TAG_TYPE_ tag;
   _stk_claim_();
   _stk_peek_EXP_(tbl);
   nam = _ag_get_TBL_NAM_(tbl);
   idx = _ag_get_TBL_IDX_(tbl);
   _dct_locate_(nam, dct, _DCT_);
   tab = _ag_get_DCT_VAL_(dct);
   tag = _ag_get_TAG_(tbl);
     if (tag == _TAB_TAG_) {  //now matrices are not first-class types.
      _stk_poke_EXP_(tab);
      _stk_push_EXP_(idx);
      _stk_poke_CNT_(REF);
      _stk_push_CNT_(EXP); }
     else
         _error_(_NMA_ERROR_);}

/*----------------------------------------------------------------------------*/
/*  MTX                                                                       */
/*     expr-stack: [... ... ... ... ... MTX] -> [TAB *0* DIM TAB *1* NBR EXP] */
/*     cont-stack: [... ... ... ... ... MTX] -> [... ... ... ... REF IXM EXP] */
/*----------------------------------------------------------------------------*/
static _NIL_TYPE_ MTX(_NIL_TYPE_)
{ _EXP_TYPE_ dct, tab, nam, mat, mtx, dim, siz, dat;
  _UNS_TYPE_ tab_siz, dim_siz;
  _stk_claim_();
  _mem_claim_();
  _stk_peek_EXP_(mtx);
  nam = _ag_get_MTX_NAM_(mtx);
  tab = _ag_get_MTX_DIM_(mtx);
  _dct_locate_(nam, dct, _DCT_);
  mat = _ag_get_DCT_VAL_(dct);
  dim = _ag_get_MAT_DIM_(mat);
  dat = _ag_get_MAT_TAB_(mat);
  tab_siz = _ag_get_TAB_SIZ_(tab);
  dim_siz = _ag_get_TAB_SIZ_(dim);
  if (tab_siz == dim_siz)
    { siz = _ag_make_NBU_(tab_siz);
      _stk_poke_EXP_(mat);
      _stk_push_EXP_(_ZERO_);
      _stk_push_EXP_(dim);
      _stk_push_EXP_(tab);
      _stk_push_EXP_(_ONE_);
      _stk_push_EXP_(siz);
      _stk_push_EXP_(_ag_get_TAB_EXP_(tab, tab_siz));
      _stk_poke_CNT_(MEF);
      _stk_push_CNT_(IXM);
      _stk_push_CNT_(EXP);
    } else
   _error_(_NMA_ERROR_); }
    

/*
 Calculates the index in the flat table of the matrix based on the dimension of the MTX.
 (EXP = exp that needs to be put on the index that we're calculating (only when it's a SET))
 MAT = the matrix with all the data
 IDX = the total index that we're calculating
 DIM = the dimension table of the matrix
 TAB = the indexes of that the user gave
 NBR = the multiplicator (for calculating the total index)
 NBR = the current index in the DIM and TAB table
 VAL = the current evaluated index to calculate the total index
 */
/*------------------------------------------------------------------------------------*/
/*  IXM                                                                               */
/*     expr-stack: [MAT IDX DIM TAB NBR NBR VAL] -> [... MAT IDX DIM TAB NBR NBR EXP] */
/*     cont-stack: [... ... ... ... ... MEF IXM] -> [... ... ... ... ... ... IXM EXP] */
/*                                                                                    */
/*     expr-stack: [MAT IDX DIM TAB NBR NBR VAL] -> [... ... ... ... ... ... MAT NBR] */
/*     cont-stack: [... ... ... ... ... MEF IXM] -> [... ... ... ... ... ... ... MEF] */
/*                                                                                    */
/*     expr-stack: [MAT IDX DIM TAB NBR NBR VAL] -> [EXP MAT IDX DIM TAB NBR NBR EXP] */
/*     cont-stack: [... ... ... ... MPL MWP IXM] -> [... ... ... ... MPL MWP IXM EXP] */
/*                                                                                    */
/*     expr-stack: [MAT IDX DIM TAB NBR NBR VAL] -> [... ... ... ... ... EXP MAT NBR] */
/*     cont-stack: [... ... ... ... MPL MWP IXM] -> [... ... ... ... ... ... MPL MWP] */
/*------------------------------------------------------------------------------------*/
static _NIL_TYPE_ IXM(_NIL_TYPE_)
{ _EXP_TYPE_ exp, idx, mul, tab, dim, tot;
  _UNS_TYPE_ val, idx_val, dim_val, siz, tot_val, mul_val;
  _TAG_TYPE_ tag;
  _stk_claim_();
  _mem_claim_();
  _stk_pop_EXP_(exp);
  _stk_pop_EXP_(idx);
  idx_val = _ag_get_NBU_(idx);
  tag = _ag_get_TAG_(exp);
    if (tag == _NBR_TAG_)
      { val = _ag_get_NBU_(exp);
        if (!(val < 1))
          { _stk_pop_EXP_(mul);
            _stk_pop_EXP_(tab);
            _stk_pop_EXP_(dim);
            _stk_peek_EXP_(tot);
            dim_val = _ag_get_NBU_(_ag_get_TAB_EXP_(dim, idx_val));
            if (val <= dim_val)
             {  siz = _ag_get_TAB_SIZ_(tab);
                if (idx_val != siz)
                  { val -= 1; }
                tot_val = _ag_get_NBU_(tot);
                mul_val = _ag_get_NBU_(mul);
                tot_val += (val*mul_val);
                mul_val *= _ag_get_NBU_(_ag_get_TAB_EXP_(dim, idx_val));
                idx_val -= 1;
                if (idx_val == 0)
                 { _stk_poke_EXP_(_ag_make_NBU_(tot_val));
                   _stk_zap_CNT_();
                 } else {
                _stk_poke_EXP_(_ag_make_NBU_(tot_val));
                _stk_push_EXP_(dim);
                _stk_push_EXP_(tab);
                _stk_push_EXP_(_ag_make_NBU_(mul_val));
                _stk_push_EXP_(_ag_make_NBU_(idx_val));
                _stk_push_EXP_(_ag_get_TAB_EXP_(tab, idx_val));
                _stk_push_CNT_(EXP);
                 }
              } else
               _error_(_RNG_ERROR_);
           } else
          _error_(_IIX_ERROR_);
       } else
    _error_(_IIX_ERROR_); }

/*------------------------------------------------------------------------*/
/*  VAR                                                                   */
/*     expr-stack: [... ... ... ... ... VAR] -> [... ... ... ... ... VAL] */
/*     cont-stack: [... ... ... ... ... VAR] -> [... ... ... ... ... ...] */
/*------------------------------------------------------------------------*/
static _NIL_TYPE_ VAR(_NIL_TYPE_)
 { _EXP_TYPE_ dct, nam, val, var;
   _stk_peek_EXP_(var);
   nam = _ag_get_VAR_NAM_(var);
   _dct_locate_(nam, dct, _DCT_);
   val = _ag_get_DCT_VAL_(dct);
   _stk_poke_EXP_(val);
   _stk_zap_CNT_(); }
  
/* public functions */

/*------------------------------------------------------------------------*/
/*  CAL                                                                   */
/*     expr-stack: [... ... ... ... FUN ARG] -> [... ... ... ... DCT EXP] */
/*     cont-stack: [... ... ... ... ... CAL] -> [... ... ... ... RET EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... FUN ARG] -> [... ... ... ... ... EXP] */
/*     cont-stack: [... ... ... ... ... CAL] -> [... ... ... ... ... EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... FUN ARG] -> [EXP DCT ARG TAB *1* EXP] */
/*     cont-stack: [... ... ... ... ... CAL] -> [... ... ... ... ATV EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... FUN ARG] -> [EXP DCT ARG TAB *1* APL] */
/*     cont-stack: [... ... ... ... ... CAL] -> [... ... ... ... ... ATA] */
/*                                                                        */
/*     expr-stack: [... ... ... ... FUN ARG] -> [EXP PAR ARG *1* DCT EXP] */
/*     cont-stack: [... ... ... ... ... CAL] -> [... ... ... ... BND EXP] */
/*                                                                        */
/*     expr-stack: [... ... ... ... FUN ARG] -> [EXP PAR ARG *1* DCT FUN] */
/*     cont-stack: [... ... ... ... ... CAL] -> [... ... ... ... ... BND] */
/*------------------------------------------------------------------------*/
_NIL_TYPE_ _eval_CAL_(_NIL_TYPE_)
 { _EXP_TYPE_ act, arg, dct, exp, frm, fun, nam, par, tab, xdc, xfu;
   _CNT_TYPE_ cnt;
   _TAG_TYPE_ tag, xtg;
   _UNS_TYPE_ siz, xsz;
   _stk_claim_();
   _stk_peek_EXP_(arg);
   tag = _ag_get_TAG_(arg);
   if (tag != _TAB_TAG_)  
     { _stk_zap_EXP_();
       _stk_peek_EXP_(fun);
       _error_msg_(_NAT_ERROR_, _ag_get_FUN_NAM_(fun)); }
   siz = _ag_get_TAB_SIZ_(arg);
   _mem_claim_SIZ_(siz);
   _stk_pop_EXP_(arg);
   if (siz == 0)
     { _stk_peek_EXP_(fun);
       par = _ag_get_FUN_ARG_(fun);
       tag = _ag_get_TAG_(par);
       switch (tag)
         { case _VAR_TAG_:
           case _APL_TAG_:
             dct = _ag_make_DCT_();
             par = _ag_get_FUN_ARG_(fun);
             nam = _ag_get_VAR_NAM_(par); 
             _ag_set_DCT_NAM_(dct, nam);
             _ag_set_DCT_VAL_(dct, _EMPTY_);
             xdc = _ag_get_FUN_DCT_(fun);
             _ag_set_DCT_DCT_(dct, xdc);
             break;
           case _TAB_TAG_:
             xsz = _ag_get_TAB_SIZ_(par);
             if (xsz == 0)
               dct = _ag_get_FUN_DCT_(fun);
             else
               _error_msg_(_NMA_ERROR_, _ag_get_FUN_NAM_(fun));
             break;
           default:
             _error_msg_(_IPM_ERROR_, _ag_get_FUN_NAM_(fun)); }
       exp = _ag_get_FUN_EXP_(fun);
       _stk_zap_CNT_();
       _stk_peek_CNT_(cnt);
       if (cnt != RET)
         { _stk_poke_EXP_(_DCT_);
           _stk_push_EXP_(exp); 
           _stk_push_CNT_(RET); }
       else
         _stk_poke_EXP_(exp);
       _stk_push_CNT_(EXP); 
       _DCT_ = dct; }
   else
     { dct = _ag_make_DCT_();
       _stk_peek_EXP_(fun);
       par = _ag_get_FUN_ARG_(fun);
       exp = _ag_get_FUN_EXP_(fun);
       xdc = _ag_get_FUN_DCT_(fun);
       tag = _ag_get_TAG_(par);
       switch (tag)
         { case _VAR_TAG_:
             nam = _ag_get_VAR_NAM_(par); 
             _ag_set_DCT_NAM_(dct, nam);
             _ag_set_DCT_DCT_(dct, xdc);
             _stk_poke_EXP_(exp);
             _stk_push_EXP_(dct);
             _stk_push_EXP_(arg);
             tab = _ag_make_TAB_(siz);
             act = _ag_get_TAB_EXP_(arg, 1);
             _stk_push_EXP_(tab);
             _stk_push_EXP_(_ONE_);
             _stk_push_EXP_(act);
             _stk_poke_CNT_(ATV);
             _stk_push_CNT_(EXP);
             break; 
           case _APL_TAG_:
             nam = _ag_get_APL_NAM_(par); 
             _ag_set_DCT_NAM_(dct, nam);
             _ag_set_DCT_DCT_(dct, xdc);
             _stk_poke_EXP_(exp);
             _stk_push_EXP_(dct);
             _stk_push_EXP_(arg);
             tab = _ag_make_TAB_(siz);
             _stk_push_EXP_(tab);
             _stk_push_EXP_(_ONE_);
             _stk_push_EXP_(par);
             _stk_poke_CNT_(ATA);
             break; 
           case _TAB_TAG_:
             xsz = _ag_get_TAB_SIZ_(par);
             if (siz != xsz)
               _error_msg_(_NMA_ERROR_, _ag_get_FUN_NAM_(fun));
             frm = _ag_get_TAB_EXP_(par, 1);
             xtg = _ag_get_TAG_(frm);
             switch (xtg)
              { case _VAR_TAG_:
                  act = _ag_get_TAB_EXP_(arg, 1);
                  _stk_poke_EXP_(exp);
                  _stk_push_EXP_(par);
                  _stk_push_EXP_(arg);
                  _stk_push_EXP_(_ONE_);
                  nam = _ag_get_VAR_NAM_(frm);
                  _ag_set_DCT_NAM_(dct, nam);
                  _ag_set_DCT_DCT_(dct, xdc);
                  _stk_push_EXP_(dct);
                  _stk_push_EXP_(act);
                  _stk_poke_CNT_(BND);
                  _stk_push_CNT_(EXP);
                  break;
                case _APL_TAG_:
                  xfu = _ag_make_FUN_();
                  par = _ag_get_FUN_ARG_(fun);
                  exp = _ag_get_FUN_EXP_(fun);
                  xdc = _ag_get_FUN_DCT_(fun);
                  act = _ag_get_TAB_EXP_(arg, 1);
                  frm = _ag_get_TAB_EXP_(par, 1);
                  _stk_poke_EXP_(exp);
                  _stk_push_EXP_(par);
                  _stk_push_EXP_(arg);
                  _stk_push_EXP_(_ONE_);
                  nam = _ag_get_APL_NAM_(frm);
                  arg = _ag_get_APL_ARG_(frm);
                  _ag_set_DCT_NAM_(dct, nam);
                  _ag_set_DCT_DCT_(dct, xdc);
                  _stk_push_EXP_(dct);
                  _ag_set_FUN_NAM_(xfu, nam);
                  _ag_set_FUN_ARG_(xfu, arg);
                  _ag_set_FUN_EXP_(xfu, act);
                  _ag_set_FUN_DCT_(xfu, _DCT_);
                  _stk_push_EXP_(xfu);
                  _stk_poke_CNT_(BND);
                   break; 
                default: 
                  _error_msg_(_IPM_ERROR_, _ag_get_FUN_NAM_(fun)); }
             break;
           default:
             _error_msg_(_IPM_ERROR_, _ag_get_FUN_NAM_(fun)); }}}
   
/*------------------------------------------------------------------------*/
/*  EXP                                                                   */
/*     expr-stack: [... ... ... ... ... EXP] -> [... ... ... ... ... EXP] */
/*     cont-stack: [... ... ... ... ... EXP] -> [... ... ... ... ... ***] */
/*------------------------------------------------------------------------*/ 
_NIL_TYPE_ _eval_EXP_(_NIL_TYPE_)
 { _EXP_TYPE_ exp;
   _TAG_TYPE_ tag;
   _stk_peek_EXP_(exp);
   tag = _ag_get_TAG_(exp);
   _stk_poke_CNT_(CNT_tab[tag]); }

