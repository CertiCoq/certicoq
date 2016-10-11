
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 37%positive.
Definition ___builtin_annot_intval : ident := 38%positive.
Definition ___builtin_bswap : ident := 61%positive.
Definition ___builtin_bswap16 : ident := 63%positive.
Definition ___builtin_bswap32 : ident := 62%positive.
Definition ___builtin_clz : ident := 64%positive.
Definition ___builtin_clzl : ident := 65%positive.
Definition ___builtin_clzll : ident := 66%positive.
Definition ___builtin_ctz : ident := 67%positive.
Definition ___builtin_ctzl : ident := 68%positive.
Definition ___builtin_ctzll : ident := 69%positive.
Definition ___builtin_debug : ident := 82%positive.
Definition ___builtin_fabs : ident := 35%positive.
Definition ___builtin_fmadd : ident := 73%positive.
Definition ___builtin_fmax : ident := 71%positive.
Definition ___builtin_fmin : ident := 72%positive.
Definition ___builtin_fmsub : ident := 74%positive.
Definition ___builtin_fnmadd : ident := 75%positive.
Definition ___builtin_fnmsub : ident := 76%positive.
Definition ___builtin_fsqrt : ident := 70%positive.
Definition ___builtin_membar : ident := 39%positive.
Definition ___builtin_memcpy_aligned : ident := 36%positive.
Definition ___builtin_nop : ident := 81%positive.
Definition ___builtin_read16_reversed : ident := 77%positive.
Definition ___builtin_read32_reversed : ident := 78%positive.
Definition ___builtin_va_arg : ident := 41%positive.
Definition ___builtin_va_copy : ident := 42%positive.
Definition ___builtin_va_end : ident := 43%positive.
Definition ___builtin_va_start : ident := 40%positive.
Definition ___builtin_write16_reversed : ident := 79%positive.
Definition ___builtin_write32_reversed : ident := 80%positive.
Definition ___compcert_va_composite : ident := 47%positive.
Definition ___compcert_va_float64 : ident := 46%positive.
Definition ___compcert_va_int32 : ident := 44%positive.
Definition ___compcert_va_int64 : ident := 45%positive.
Definition ___i64_dtos : ident := 48%positive.
Definition ___i64_dtou : ident := 49%positive.
Definition ___i64_sar : ident := 60%positive.
Definition ___i64_sdiv : ident := 54%positive.
Definition ___i64_shl : ident := 58%positive.
Definition ___i64_shr : ident := 59%positive.
Definition ___i64_smod : ident := 56%positive.
Definition ___i64_stod : ident := 50%positive.
Definition ___i64_stof : ident := 52%positive.
Definition ___i64_udiv : ident := 55%positive.
Definition ___i64_umod : ident := 57%positive.
Definition ___i64_utod : ident := 51%positive.
Definition ___i64_utof : ident := 53%positive.
Definition ___sFILE : ident := 25%positive.
Definition ___sFILEX : ident := 17%positive.
Definition ___sbuf : ident := 3%positive.
Definition ___stderrp : ident := 86%positive.
Definition ___stringlit_1 : ident := 96%positive.
Definition ___stringlit_2 : ident := 97%positive.
Definition ___stringlit_3 : ident := 98%positive.
Definition ___stringlit_4 : ident := 99%positive.
Definition ___stringlit_5 : ident := 101%positive.
Definition __base : ident := 1%positive.
Definition __bf : ident := 9%positive.
Definition __blksize : ident := 23%positive.
Definition __close : ident := 12%positive.
Definition __cookie : ident := 11%positive.
Definition __extra : ident := 18%positive.
Definition __file : ident := 8%positive.
Definition __flags : ident := 7%positive.
Definition __lb : ident := 22%positive.
Definition __lbfsize : ident := 10%positive.
Definition __nbuf : ident := 21%positive.
Definition __offset : ident := 24%positive.
Definition __p : ident := 4%positive.
Definition __r : ident := 5%positive.
Definition __read : ident := 13%positive.
Definition __seek : ident := 14%positive.
Definition __size : ident := 2%positive.
Definition __ub : ident := 16%positive.
Definition __ubuf : ident := 20%positive.
Definition __ur : ident := 19%positive.
Definition __w : ident := 6%positive.
Definition __write : ident := 15%positive.
Definition _abort : ident := 88%positive.
Definition _alloc : ident := 28%positive.
Definition _argc : ident := 27%positive.
Definition _args : ident := 26%positive.
Definition _exit : ident := 83%positive.
Definition _fi : ident := 90%positive.
Definition _fprintf : ident := 87%positive.
Definition _free : ident := 84%positive.
Definition _free_heap : ident := 103%positive.
Definition _garbage_collect : ident := 102%positive.
Definition _gc : ident := 105%positive.
Definition _h : ident := 92%positive.
Definition _heap : ident := 30%positive.
Definition _hi : ident := 94%positive.
Definition _limit : ident := 29%positive.
Definition _lo : ident := 93%positive.
Definition _main : ident := 106%positive.
Definition _malloc : ident := 85%positive.
Definition _next : ident := 33%positive.
Definition _num_allocs : ident := 95%positive.
Definition _printf : ident := 89%positive.
Definition _reset_heap : ident := 104%positive.
Definition _resume : ident := 100%positive.
Definition _space : ident := 34%positive.
Definition _start : ident := 32%positive.
Definition _thread_info : ident := 31%positive.
Definition _ti : ident := 91%positive.
Definition _t'1 : ident := 107%positive.
Definition _t'2 : ident := 108%positive.
Definition _t'3 : ident := 109%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 52);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 33) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 39) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stderrp := {|
  gvar_info := (tptr (Tstruct ___sFILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_lo, (tptr tint)) ::
               (_hi, (tptr tint)) :: (_num_allocs, tuint) :: (_t'3, tvoid) ::
               (_t'2, tint) :: (_t'1, tvoid) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sset _num_allocs
      (Ederef
        (Ebinop Oadd (Etempvar _fi (tptr tuint))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sifthenelse (Etempvar _h (tptr (Tstruct _heap noattr)))
        (Sset _t'1
          (Ecast (Ecast (Econst_int (Int.repr 0) tint) tvoid) tvoid))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_3 (tarray tschar 30)) ::
               (Evar ___stringlit_2 (tarray tschar 9)) ::
               (Econst_int (Int.repr 32) tint) ::
               (Evar ___stringlit_1 (tarray tschar 2)) :: nil))
            (Scall (Some _t'3)
              (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
          (Sset _t'1 (Ecast (Etempvar _t'3 tvoid) tvoid))))
      (Ssequence
        (Sset _lo
          (Efield
            (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
              (Tstruct _heap noattr)) _start (tptr tint)))
        (Ssequence
          (Sset _hi
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                (Tstruct _heap noattr)) _limit (tptr tint)))
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Osub (Etempvar _hi (tptr tint))
                             (Etempvar _lo (tptr tint)) tint)
                           (Etempvar _num_allocs tuint) tint)
              (Ssequence
                (Scall None
                  (Evar _fprintf (Tfunction
                                   (Tcons (tptr (Tstruct ___sFILE noattr))
                                     (Tcons (tptr tschar) Tnil)) tint
                                   {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                  ((Evar ___stderrp (tptr (Tstruct ___sFILE noattr))) ::
                   (Evar ___stringlit_4 (tarray tschar 45)) :: nil))
                (Scall None
                  (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
                  ((Econst_int (Int.repr 1) tint) :: nil)))
              Sskip)
            (Ssequence
              (Sassign
                (Ederef
                  (Efield
                    (Ederef
                      (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                      (Tstruct _thread_info noattr)) _alloc
                    (tptr (tptr tint))) (tptr tint))
                (Etempvar _lo (tptr tint)))
              (Sassign
                (Ederef
                  (Efield
                    (Ederef
                      (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                      (Tstruct _thread_info noattr)) _limit
                    (tptr (tptr tint))) (tptr tint))
                (Etempvar _hi (tptr tint))))))))))
|}.

Definition f_garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Esizeof (Tstruct _heap noattr) tuint) :: nil))
        (Sset _h
          (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _heap noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
              (Tstruct _heap noattr)) _start (tptr tint))
          (Efield
            (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
              (Tstruct _heap noattr)) _space (tarray tint 16777216)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                (Tstruct _heap noattr)) _next (tptr tint))
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                (Tstruct _heap noattr)) _space (tarray tint 16777216)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                  (Tstruct _heap noattr)) _limit (tptr tint))
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                    (Tstruct _heap noattr)) _space (tarray tint 16777216))
                (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                  (Econst_int (Int.repr 24) tint) tint) (tptr tint)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _heap
                  (tptr (Tstruct _heap noattr)))
                (Etempvar _h (tptr (Tstruct _heap noattr))))
              (Ssequence
                (Scall None
                  (Evar _resume (Tfunction
                                  (Tcons (tptr tuint)
                                    (Tcons
                                      (tptr (Tstruct _thread_info noattr))
                                      Tnil)) tvoid cc_default))
                  ((Etempvar _fi (tptr tuint)) ::
                   (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                   nil))
                (Sreturn None)))))))
    (Ssequence
      (Scall None
        (Evar _fprintf (Tfunction
                         (Tcons (tptr (Tstruct ___sFILE noattr))
                           (Tcons (tptr tschar) Tnil)) tint
                         {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
        ((Evar ___stderrp (tptr (Tstruct ___sFILE noattr))) ::
         (Evar ___stringlit_5 (tarray tschar 52)) :: nil))
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil)))))
|}.

Definition f_free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil))
|}.

Definition f_reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
      (Tstruct _heap noattr)) _next (tptr tint))
  (Efield
    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
      (Tstruct _heap noattr)) _start (tptr tint)))
|}.

Definition f_gc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _garbage_collect (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tstruct _thread_info noattr))
                               Tnil)) tvoid cc_default))
  ((Etempvar _fi (tptr tuint)) ::
   (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))
|}.

Definition composites : list composite_definition :=
(Composite ___sbuf Struct
   ((__base, (tptr tuchar)) :: (__size, tint) :: nil)
   noattr ::
 Composite ___sFILE Struct
   ((__p, (tptr tuchar)) :: (__r, tint) :: (__w, tint) ::
    (__flags, tshort) :: (__file, tshort) ::
    (__bf, (Tstruct ___sbuf noattr)) :: (__lbfsize, tint) ::
    (__cookie, (tptr tvoid)) ::
    (__close, (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))) ::
    (__read,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
             tint cc_default))) ::
    (__seek,
     (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))
             tlong cc_default))) ::
    (__write,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
             tint cc_default))) :: (__ub, (Tstruct ___sbuf noattr)) ::
    (__extra, (tptr (Tstruct ___sFILEX noattr))) :: (__ur, tint) ::
    (__ubuf, (tarray tuchar 3)) :: (__nbuf, (tarray tuchar 1)) ::
    (__lb, (Tstruct ___sbuf noattr)) :: (__blksize, tint) ::
    (__offset, tlong) :: nil)
   noattr ::
 Composite _thread_info Struct
   ((_args, (tptr tint)) :: (_argc, tint) :: (_alloc, (tptr (tptr tint))) ::
    (_limit, (tptr (tptr tint))) :: (_heap, (tptr (Tstruct _heap noattr))) ::
    nil)
   noattr ::
 Composite _heap Struct
   ((_start, (tptr tint)) :: (_next, (tptr tint)) :: (_limit, (tptr tint)) ::
    (_space, (tarray tint 16777216)) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (___stderrp, Gvar v___stderrp) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct ___sFILE noattr)) (Tcons (tptr tschar) Tnil)) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil None cc_default)) Tnil
     tvoid cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_resume, Gfun(Internal f_resume)) ::
 (_garbage_collect, Gfun(Internal f_garbage_collect)) ::
 (_free_heap, Gfun(Internal f_free_heap)) ::
 (_reset_heap, Gfun(Internal f_reset_heap)) :: (_gc, Gfun(Internal f_gc)) ::
 nil);
prog_public :=
(_gc :: _reset_heap :: _free_heap :: _garbage_collect :: _resume ::
 _printf :: _abort :: _fprintf :: ___stderrp :: _malloc :: _free :: _exit ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod ::
 ___i64_smod :: ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof ::
 ___i64_utod :: ___i64_stod :: ___i64_dtou :: ___i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

