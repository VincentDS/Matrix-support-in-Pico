/*-----------------------------------*/
/*             >>>Pico<<<            */
/*            Theo D'Hondt           */
/*   VUB Programming Technology Lab  */
/*             (c) 1997              */
/*-----------------------------------*/
/*            Environments           */
/*-----------------------------------*/

/* public macros */

#define _dct_locate_(NAM, dct, DCT)\
  for (dct = DCT; !_mem_is_same_(NAM, _ag_get_DCT_NAM_(dct));\
       dct = _ag_get_DCT_DCT_(dct))\
    if (_ag_is_VOI_(dct))\
      _error_msg_(_UDI_ERROR_, NAM);
      
#define _stk_claim_()\
  if (_CNT_ - _EXP_ <= _STK_CLAIM_) _env_expand_()

#define _stk_poke_CNT_(CNT)\
  *(_CNT_TYPE_ *)_CNT_ = CNT

#ifdef NDEBUG

#define _stk_push_CNT_(CNT)\
  { _CNT_ -= _EXP_SIZE_;\
    _stk_poke_CNT_(CNT); }

#else

#define _stk_push_CNT_(CNT)\
  { _CNT_ -= _EXP_SIZE_;\
    if (_CNT_ <= _EXP_)\
      _error_(_STK_ERROR_);\
    _stk_poke_CNT_(CNT); }
    
#endif

#define _stk_peek_CNT_(CNT)\
  CNT =  *(_CNT_TYPE_ *)_CNT_

#define _stk_zap_CNT_()\
  _CNT_ += _EXP_SIZE_

#define _stk_pop_CNT_(CNT)\
  { _stk_peek_CNT_(CNT);\
    _stk_zap_CNT_(); }
      
#define _stk_poke_EXP_(EXP)\
  *(_EXP_TYPE_ *)_EXP_ = EXP

#ifdef NDEBUG

#define _stk_push_EXP_(EXP)\
  { _EXP_ += _EXP_SIZE_;\
    _stk_poke_EXP_(EXP); }

#else

#define _stk_push_EXP_(EXP)\
  { _EXP_ += _EXP_SIZE_;\
	  if (_EXP_ >= _CNT_ )\
	    _error_(_STK_ERROR_);\
    _stk_poke_EXP_(EXP); }

#endif

#define _stk_peek_EXP_(EXP)\
  EXP = *(_EXP_TYPE_ *)_EXP_

#define _stk_zap_EXP_()\
  { _stk_poke_EXP_(_VOID_);\
    _EXP_ -= _EXP_SIZE_; }

#define _stk_pop_EXP_(EXP)\
  { _stk_peek_EXP_(EXP);\
    _stk_zap_EXP_(); }
      
#define _stk_loop_()\
  { LOOP: (*(_CNT_TYPE_ *)_CNT_)(); goto LOOP; }     

/* public variables */

extern _EXP_TYPE_ _DCT_;
extern _UNS_TYPE_ _CNT_;
extern _UNS_TYPE_ _EXP_;
extern _EXP_TYPE_ _STK_;
                           
/* public prototypes */

_NIL_TYPE_      _env_setup_(const _SIZ_TYPE_);

_EXP_TYPE_   _env_make_NAM_(const _STR_TYPE_);

_EXP_TYPE_ _env_initialise_(const _EXP_TYPE_);

_NIL_TYPE_    _env_capture_(const _EXP_TYPE_);

_NIL_TYPE_    _env_restore_(const _EXP_TYPE_);

_NIL_TYPE_     _env_expand_(      _NIL_TYPE_);

_NIL_TYPE_      _env_save_(const _EXP_TYPE_);

_NIL_TYPE_      _env_load_(const _EXP_TYPE_);
