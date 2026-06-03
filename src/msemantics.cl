mod Msemantics logic: 'cl'

incl Mtex

incl Maux

incl Msyntax

incl Mdebug

rem 
  \para \bf  Aritmetizácia sémantiky  \end 

rem 
  \para \header* fun/2 Inl 'Tex_p2_inl' \end Konštruktory pravidiel pre 
  odvodenie, že slovo \ft w \end patrí do jazyka regulárneho výrazu 
  \ft r \end: \ft Inl(w,r) \end 

fun/0 Os 'Tex_f0_sq_inl_oe_def'
  Os = 0,0

fun Cs 'Tex_f1_sq_inl_char'
  Cs(x) = 1,x

fun Es 'Tex_f1_sq_inl_se_def'
  Es(r) = 2,r

rem 
  \para \header* fun/4 Ls 'Tex_f4_sq_inl_pe_lt' \end pravidlo pre ľavý regex 
  zjednotenia 
  \eq* 
    Ls(S_foo(w,r1),w,r1,r2)
  \end

fun/4 Ls 'Tex_f4_sq_inl_pe_lt'
  Ls(d,w,r1,r2) = 3,d,w,r1,r2

rem 
  \para \header* fun/4 Rs 'Tex_f4_sq_inl_pe_rt' \end pravidlo pre pravý regex 
  zjednotenia 
  \eq* 
    Rs(S_foo(w,r2),w,r1,r2)
  \end

fun/4 Rs 'Tex_f4_sq_inl_pe_rt'
  Rs(d,w,r1,r2) = 4,d,w,r1,r2

rem 
  \para \header* fun/6 Ss 'Tex_f6_sq_inl_te_split' \end pravidlo pre zreťazenie 
  \eq* 
    Ss(S_foo(w,r1),S_foo(w1,r2),w,w1,r1,r2)
  \end

fun/6 Ss 'Tex_f6_sq_inl_te_split'
  Ss(d1,d2,w,w1,r1,r2) = 5,d1,d2,w,w1,r1,r2

rem 
  \para \header* fun/5 Is 'Tex_f5_sq_inl_se_iter' \end pravidlo pre iteráciu 
  Kleeneho uzávera ak \ft w != 0 \end 
  \eq* 
    Is(S_foo(w,r),S_foo(w1,Se(r)),w,w1,r)
  \end

fun/5 Is 'Tex_f5_sq_inl_se_iter'
  Is(d1,d2,w,w1,r) = 6,d1,d2,w,w1,r

rem 
  \para \header* pred/3 Proves 'Tex_p3_proves_inl' \end 
  \header* pred/2 Inl 'Tex_p2_inl' \end Majme regulárny výraz \ft r \end a 
  slovo \ft w \end. Predikát \ft Proves(d,w,r) \end platí, ak \ft d \end je 
  dôkazový strom, ktorý dokazuje \ft Inl(w,r) \end. 

pred/3 Proves 'Tex_p3_proves_inl'
  Proves(Os,w,Oe) <- w = 0
  Proves(Cs(x),w,Ce(y)) <- w = x,0 & x = y
  Proves(Es(r),w,s) <- s = Se(r) & w = 0
  Proves(Ls(d,w1,r1,r2),w,s) <- s = Pe(r1,r2) & w = w1 & Proves(d,w,r1)
  Proves(Rs(d,w1,r1,r2),w,s) <- s = Pe(r1,r2) & w = w1 & Proves(d,w,r2)
  Proves(Ss(d1,d2,w1,w2,r1,r2),w,s) <- 
    s = Te(r1,r2) & w = w1++w2 & Proves(d1,w1,r1) & Proves(d2,w2,r2)
  Proves(Is(d1,d2,w1,w2,r),w,s) <- 
    s = Se(r) & w = w1++w2 & Proves(d1,w1,r) & Proves(d2,w2,Se(r))

rem 
  \para \bf  Slovo akceptované regulárnym výrazom  \end 

rem 
  \para \header* pred/2 Inl 'Tex_p2_inl' \end Majme regulárny výraz \ft r \end 
  a slovo \ft w \end. Predikát \ft Inl(w,r) \end platí, ak existuje odvodenie 
  \ft d \end také, že \ft Proves(d,w,r) \end. 

pred/2 Inl 'Tex_p2_inl'
  Inl(w,r) <-> \e dProves(d,w,r)

rem 
  \para Základné vlastnosti predikátu \ft Inl(w,r) \end: 

thm Inl_def
  Re(r) -> Inl(w,r) <-> \e dProves(d,w,r)
proof 
 exp Inl; w,r proved..

thm Inl_ze
  Inl(w,Ze) <-> \f
proof 
 use Inl_def.0; Ze; w
  weak Inl(w,Ze) <-> \e dProves(d,w,Ze)
   eigen* ~\e dProves(d,w,Ze); d
    inv* ~Proves(d,w,Ze)
     case Proves; d,w,Ze @ w1; x,w1,y; r,w1,s; d1,w1,r1,r2,w2,s; d1,w1,r1,r2,w2,s; d1,d2,w1,w2,
                                                                                   r1,r2,w3,s; d1,
                                                                                               d2,
                                                                                               w1,
                                                                                               w2,
                                                                                               r,
                                                                                               w3,
                                                                                               s
      proved
      proved
      proved
      proved
      proved
      proved
      proved......

thm Inl_oe
  Inl(w,Oe) <-> w = 0
proof 
 use Inl_def.0; Oe; w
  weak Inl(w,Oe) <-> \e dProves(d,w,Oe)
   split* \e dProves(d,w,Oe) <-> w = 0.2,0,0
    eigen \e dProves(d,w,Oe); d
     case Proves; d,w,Oe @ w1; x,w1,y; r,w1,s; d1,w1,r1,r2,w2,s; d1,w1,r1,r2,w2,s; d1,d2,w1,w2,
                                                                                   r1,r2,w3,s; d1,
                                                                                               d2,
                                                                                               w1,
                                                                                               w2,
                                                                                               r,
                                                                                               w3,
                                                                                               s
      proved
      proved
      proved
      proved
      proved
      proved
      proved..
    inst* \e dProves(d,0,Oe); Os proved.....

thm Inl_ce
  Inl(w,Ce(x)) <-> w = x,0
proof 
 use Inl_def.0; Ce(x); w
  weak Inl(w,Ce(x)) <-> \e dProves(d,w,Ce(x))
   split* \e dProves(d,w,Ce(x)) <-> w = x,0.2,0,0
    eigen \e dProves(d,w,Ce(x)); d
     case Proves; d,w,Ce(x) @ w1; x1,w1,y; r,w1,s; d1,w1,r1,r2,w2,s; d1,w1,r1,r2,w2,s; d1,d2,
                                                                                       w1,w2,
                                                                                       r1,r2,
                                                                                       w3,s; d1,
                                                                                             d2,
                                                                                             w1,
                                                                                             w2,
                                                                                             r,
                                                                                             w3,s
      proved
      proved
      proved
      proved
      proved
      proved
      proved..
    inst* \e dProves(d,(x,0),Ce(x)); Cs(x) proved.....

thm Inl_pe
  Re(r1) & Re(r2) -> Inl(w,Pe(r1,r2)) <-> Inl(w,r1) \/ Inl(w,r2)
proof 
 use Inl_def.0; Pe(r1,r2); w
  use Inl_def.0; r1; w
   use Inl_def.0; r2; w
    weak Inl(w,Pe(r1,r2)) <-> \e dProves(d,w,Pe(r1,r2))
     weak Inl(w,r1) <-> \e dProves(d,w,r1)
      weak Inl(w,r2) <-> \e dProves(d,w,r2)
       split* \e dProves(d,w,Pe(r1,r2)) <-> 
              \e dProves(d,w,r1) \/ \e dProves(d,w,r2).2,0,1,(4,0,0,0),0
        eigen \e dProves(d,w,Pe(r1,r2)); d
         case Proves; d,w,Pe(r1,r2) @ w1; x,w1,y; r,w1,s; d1,w1,r3,r4,w2,s; d1,w1,r3,r4,w2,s; d1,
                                                                                              d2,
                                                                                              w1,
                                                                                              w2,
                                                                                              r3,
                                                                                              r4,
                                                                                              w3,
                                                                                              s; d1,
                                                                                                 d2,
                                                                                                 w1,
                                                                                                 w2,
                                                                                                 r,
                                                                                                 w3,
                                                                                                 s
          proved
          proved
          proved
          inst* \e dProves(d,w1,r3); d1 proved.
          inst* \e dProves(d,w1,r4); d1 proved.
          proved
          proved..
        eigen \e dProves(d,w,r1); d
         inst* \e dProves(d,w,Pe(r1,r2)); Ls(d,w,r1,r2) proved..
        eigen \e dProves(d,w,r2); d
         inst* \e dProves(d,w,Pe(r1,r2)); Rs(d,w,r1,r2) proved..........

thm Inl_te
  Re(r1) & Re(r2) -> Inl(w,Te(r1,r2)) <-> 
  \e w1\e w2(w = w1++w2 & Inl(w1,r1) & Inl(w2,r2))
proof 
 use Inl_def.0; Te(r1,r2); w
  weak Inl(w,Te(r1,r2)) <-> \e dProves(d,w,Te(r1,r2))
   cut* \e dProves(d,w,Te(r1,r2)) <-> 
        \e d1\e d2\e w1\e w2Proves(Ss(d1,d2,w1,w2,r1,r2),w,Te(r1,r2))
    weak* \e dProves(d,w,Te(r1,r2)) <-> 
          \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1))
     split* \e dProves(d,w,Te(r1,r2)) <-> 
            \e w1(\e d1Proves(d1,w1,r1) & 
                  \e w2(\e d2Proves(d2,w2,r2) & w = w1++w2)).2,0,0
      eigen \e dProves(d,w,Te(r1,r2)); d
       case Proves; d,w,Te(r1,r2) @ w1; x,w1,y; r,w1,s; d1,w1,r3,r4,w2,s; d1,w1,r3,r4,w2,s; d1,
                                                                                            d2,
                                                                                            w1,
                                                                                            w2,
                                                                                            r3,
                                                                                            r4,
                                                                                            w3,
                                                                                            s; d1,
                                                                                               d2,
                                                                                               w1,
                                                                                               w2,
                                                                                               r,
                                                                                               w3,
                                                                                               s
        proved
        proved
        proved
        proved
        proved
        inst* \e w3(\e d1Proves(d1,w3,r3) & 
                    \e w4(\e d2Proves(d2,w4,r4) & w1++w2 = w3++w4)):0,3,0,
                                                                    (0,3,0,1,0),0; w1; d1; w2; d2 proved.
        proved..
      eigen \e w1(\e d1Proves(d1,w1,r1) & 
                  \e w2(\e d2Proves(d2,w2,r2) & w = w1++w2)).0:0,3,0,
                                                               (0,3,0,1,0),0; w1,
                                                                              d1,
                                                                              w2,
                                                                              d2
       inst* \e dProves(d,w1++w2,Te(r1,r2)); Ss(d1,d2,w1,w2,r1,r2) proved....
    weak \e dProves(d,w,Te(r1,r2)) <-> 
         \e w1(\e d1Proves(d1,w1,r1) & \e w2(\e d2Proves(d2,w2,r2) & w = w1++w2))
     split* \e w1(\e d1Proves(d1,w1,r1) & 
                  \e w2(\e d2Proves(d2,w2,r2) & w = w1++w2)) <-> 
            \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)).2,0,0
      eigen \e w1(\e d1Proves(d1,w1,r1) & 
                  \e w2(\e d2Proves(d2,w2,r2) & w = w1++w2)).0:0,3,1,0,0; w1,
                                                                          w2
       inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r2)) & Inl(w3,r1)):0,3,0,1,0; w1; w2
        weak* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r2)) & Inl(w3,r1))
         use Inl_def.1,0,2,1,0:0; r1; w1
          use Inl_def.1,0,2,1,0:0; r2; w2 proved.....
      eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)).0:0,3,0,1,0; w1,
                                                                            w2
       inst* \e w3(\e d1Proves(d1,w3,r1) & 
                   \e w4(\e d2Proves(d2,w4,r2) & w1++w2 = w3++w4)):0,3,1,0,0; w1; w2
        weak* \e w3(\e d1Proves(d1,w3,r1) & 
                    \e w4(\e d2Proves(d2,w4,r2) & w1++w2 = w3++w4))
         use Inl_def.1,0,2,0,0; r1; w1
          use Inl_def.1,0,2,0,0; r2; w2 proved...........

thm Inl_se_ie
  Re(r) -> Inl(w,Se(r)) <-> \e nInl(w,Ie(r,n))
proof 
 use Inl_def.0; Se(r); w
  weak Inl(w,Se(r)) <-> \e dProves(d,w,Se(r))
   split* \e dProves(d,w,Se(r)) <-> \e nInl(w,Ie(r,n)).2,0,0
    eigen \e dProves(d,w,Se(r)); d
     indm |d|; w @ d1
      case Proves; d,w,Se(r) @ w1; x,w1,y; r1,w1,s; d1,w1,r1,r2,w2,s; d1,w1,r1,r2,w2,s; d1,d2,
                                                                                        w1,w2,
                                                                                        r1,r2,
                                                                                        w3,s; d1,
                                                                                              d2,
                                                                                              w1,
                                                                                              w2,
                                                                                              r1,
                                                                                              w3,
                                                                                              s
       proved
       proved
       inst* \e nInl(0,Ie(r1,n)); 0
        use Inl_oe.2,1,0; 0 proved..
       proved
       proved
       proved
       inst \a d3(|d3| <= |d1|+|d2|+|r1|+|w1|+|w2|+7 -> 
                  \a w(Proves(d3,w,Se(r1)) -> \e nInl(w,Ie(r1,n)))):0,2,1,0; d2; w2
        eigen \e nInl(w2,Ie(r1,n)); n
         inst* \e nInl(w1++w2,Ie(r1,n)); n+1
          weak* \e nInl(w1++w2,Ie(r1,n))
           use Inl_def.1,0,2,1,0:0,2,1,2,0,1; r; w1; d1
            use Type_of_ie; r1; n
             use Inl_te.1,0,2,1,0:0,2,1,2,0,1; r1; Ie(r1,n); w1++w2; w1; w2 proved..........
    eigen \e nInl(w,Ie(r,n)); n
     ind N; n; w @ 0; n
      use Inl_oe.2,0,0; w
       inst* \e dProves(d,0,Se(r)); Es(r) proved..
      use Inl_te.1,0,2,0,0; r; Ie(r,n); w
       use Type_of_ie; r; n
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Ie(r,n))) & Inl(w1,r)).0:0,3,0,1,
                                                                       0; w1,
                                                                          w2
         inst \a w(Inl(w,Ie(r,n)) -> \e dProves(d,w,Se(r))); w2
          eigen \e dProves(d,w2,Se(r)); d
           use Inl_def.1,0,2,0,0; r; w1
            eigen \e dProves(d,w1,r); d1
             inst* \e dProves(d,w1++w2,Se(r)); Is(d1,d,w1,w2,r) proved..............

rem 
  \para \bf  Vlastnosti regulárnych výrazov  \end 

rem 
  \para \bf  Vlastnosti jazyka regulárneho výrazu  \end 

thm Inl_not_pe
  Re(r1) & Re(r2) -> ~Inl(w,Pe(r1,r2)) <-> ~Inl(w,r1) & ~Inl(w,r2)
proof 
 use Inl_pe.0; r1; r2; w
  split* Inl(w,r1) \/ Inl(w,r2) <-> ~(~Inl(w,r1) & ~Inl(w,r2)).2,
                                                               (1,(4,0,0,0),0),
                                                               1,(4,0,0,0),0
   proved
   proved
   proved
   proved...

thm Inl_not_te
  Re(r1) & Re(r2) -> ~Inl(0,Te(r1,r2)) <-> ~Inl(0,r1) \/ ~Inl(0,r2)
proof 
 use Inl_te.0; r1; r2; 0
  weak Inl(0,Te(r1,r2)) <-> 
       \e w1(w1 = 0 & Inl(w1,r1)) & \e w2(w2 = 0 & Inl(w2,r2))
   cut* \e w1(w1 = 0 & Inl(w1,r1)) <-> Inl(0,r1)
    weak* \e w1(w1 = 0 & Inl(w1,r1)) & \e w2(w2 = 0 & Inl(w2,r2)) <-> 
          ~(~Inl(0,r1) \/ ~Inl(0,r2))
     split* \e w1(w1 = 0 & Inl(w1,r1)) <-> Inl(0,r1).2,0,0
      eigen \e w1(w1 = 0 & Inl(w1,r1)).0; w1 proved.
      inst* \e w1(w1 = 0 & Inl(w1,r1)); 0 proved...
    cut* \e w2(w2 = 0 & Inl(w2,r2)) <-> Inl(0,r2)
     weak* Inl(0,r1) & \e w2(w2 = 0 & Inl(w2,r2)) <-> 
           ~(~Inl(0,r1) \/ ~Inl(0,r2))
      split* \e w2(w2 = 0 & Inl(w2,r2)) <-> Inl(0,r2).2,0,0
       eigen \e w2(w2 = 0 & Inl(w2,r2)).0; w2 proved.
       inst* \e w2(w2 = 0 & Inl(w2,r2)); 0 proved...
     split* Inl(0,r1) & Inl(0,r2) <-> ~(~Inl(0,r1) \/ ~Inl(0,r2)).2,
                                                                  (1,0,4,0,0,0),
                                                                  1,0,4,0,0,0
      proved
      proved
      proved
      proved......

lemma Inl_se_simp
  Re(r) & Inl(w,Te(r,Se(r))) -> Inl(w,Se(r))
proof 
 use Inl_te.1,0,2,0,0; r; Se(r); w
  cut* \e w1(\e w2(w = w1++w2 & Inl(w2,Se(r))) & Inl(w1,r)) -> 
       \e n\e w1(\e w2(w = w1++w2 & Inl(w2,Ie(r,n))) & Inl(w1,r))
   eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Se(r))) & Inl(w1,r)).0:0,3,0,1,0; w1,
                                                                           w2
    inst* \e w3(\e w4(\e nInl(w4,Ie(r,n)) & w1++w2 = w3++w4) & Inl(w3,r)):0,3,0,
                                                                          1,0; w1; w2
     use Inl_se_ie.0; r; w2 proved...
   cut* \e w1(\e w2(\e nInl(w2,Ie(r,n)) & w = w1++w2) & Inl(w1,r)) -> 
        \e nInl(w,Te(r,Ie(r,n)))
    weak* Inl(w,Se(r))
     eigen \e w1(\e w2(\e nInl(w2,Ie(r,n)) & w = w1++w2) & Inl(w1,r)).0:0,3,
                                                                        (0,3,0,
                                                                         1,0),
                                                                        1,0; w1,
                                                                             w2,
                                                                             n
      inst* \e nInl(w1++w2,Te(r,Ie(r,n))); n
       weak* \e nInl(w1++w2,Te(r,Ie(r,n)))
        use Type_of_ie; r; n
         use Inl_te.1,0,2,1,0:0,2,1,2,0,1; r; Ie(r,n); w1++w2; w1; w2 proved......
    eigen \e nInl(w,Te(r,Ie(r,n))); n
     use Inl_se_ie.1,0,2,1,0:0,2,1,2,0,1; r; w; n+1 proved......

rem 
  \para \bf  Vlastnosti rovnosti jazykov  \end 

rem 
  \para Majme regulárne výrazy \ft r \end a slovo \ft s \end, potom definujeme 
  ekvivalenicu, ktorú nazývame rovnosť regulárnych výrazov nasledovne: 

pred/2 Eql 'Tex_p2_eql'
  Eql(r,s) <-> \a w(Inl(w,r) <-> Inl(w,s))

thm Eql_def
  Re(r1) & Re(r2) -> Eql(r1,r2) <-> \a w(Inl(w,r1) <-> Inl(w,r2))
proof 
 exp Eql; r1,r2 proved..

thm Eql_refl
  Re(r) -> Eql(r,r)
proof 
 use Eql_def.0; r; r proved..

thm Eql_sym
  Re(r1) & Re(r2) -> Eql(r1,r2) -> Eql(r2,r1)
proof 
 use Eql_def.0; r1; r2
  use Eql_def.0; r2; r1 proved...

thm Eql_trans
  Re(r1) & Re(r2) & Re(r3) -> Eql(r1,r2) & Eql(r2,r3) -> Eql(r1,r3)
proof 
 use Eql_def.0; r1; r2
  use Eql_def.0; r2; r3
   use Eql_def.0; r1; r3
    eigen* \a w(Inl(w,r1) <-> Inl(w,r3)).0; w
     inst \a w(Inl(w,r1) <-> Inl(w,r2)).0; w
      inst \a w(Inl(w,r2) <-> Inl(w,r3)).0; w proved.......

rem 
  \para \bf  Kongruentné vlastnosti  \end 

thm Eql_pe_cong
  Re(r1) & Re(r2) & Re(r3) & Re(r4) & Eql(r1,r3) & Eql(r2,r4) -> 
  Eql(Pe(r1,r2),Pe(r3,r4))
proof 
 use Eql_def.0; Pe(r1,r2); Pe(r3,r4)
  eigen* \a w(Inl(w,Pe(r1,r2)) <-> Inl(w,Pe(r3,r4))).0; w
   use Inl_pe.0; r1; r2; w
    use Inl_pe.0; r3; r4; w
     use Eql_def.1,0,2,0,0:0,2,1,2,1,0; r1; r3; w
      use Eql_def.1,0,2,0,0:0,2,1,2,1,0; r2; r4; w proved.......

thm Eql_te_cong
  Re(r1) & Re(r2) & Re(r3) & Re(r4) & Eql(r1,r3) & Eql(r2,r4) -> 
  Eql(Te(r1,r2),Te(r3,r4))
proof 
 use Eql_def.0; Te(r1,r2); Te(r3,r4)
  eigen* \a w(Inl(w,Te(r1,r2)) <-> Inl(w,Te(r3,r4))).0; w
   use Inl_te.0; r1; r2; w
    use Inl_te.0; r3; r4; w
     split* \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)) <-> 
            \e w1(\e w2(w = w1++w2 & Inl(w2,r4)) & Inl(w1,r3)).2,0,0
      eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)).0:0,3,0,1,0; w1,
                                                                            w2
       use Eql_def.1,0,2,0,0:0,2,1,2,1,0; r1; r3; w1
        use Eql_def.1,0,2,0,0:0,2,1,2,1,0; r2; r4; w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r4)) & Inl(w3,r3)):0,3,0,1,0; w1; w2 proved....
      eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r4)) & Inl(w1,r3)).0:0,3,0,1,0; w1,
                                                                            w2
       use Eql_def.1,0,2,0,0:0,2,1,2,1,0; r1; r3; w1
        use Eql_def.1,0,2,0,0:0,2,1,2,1,0; r2; r4; w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r2)) & Inl(w3,r1)):0,3,0,1,0; w1; w2 proved..........

thm Eql_ie_cong
  Re(r1) & Re(r2) & Eql(r1,r2) -> Eql(Ie(r1,n),Ie(r2,n))
proof 
 use Type_of_ie; r1; n
  use Type_of_ie; r2; n
   ind N; n @ 0; n
    use Eql_refl; Oe proved.
    use Eql_te_cong; r1; Ie(r1,n); r2; Ie(r2,n) proved.....

thm Eql_se_cong
  Re(r1) & Re(r2) & Eql(r1,r2) -> Eql(Se(r1),Se(r2))
proof 
 use Eql_def.0; Se(r1); Se(r2)
  eigen* \a w(Inl(w,Se(r1)) <-> Inl(w,Se(r2))).0; w
   use Inl_se_ie.0; r1; w
    use Inl_se_ie.0; r2; w
     split* \e nInl(w,Ie(r1,n)) <-> \e nInl(w,Ie(r2,n)).2,0,0
      eigen \e nInl(w,Ie(r1,n)); n
       use Eql_ie_cong; r1; r2; n
        use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Ie(r1,n); Ie(r2,n); w
         use Type_of_ie; r1; n
          use Type_of_ie; r2; n
           inst* \e nInl(w,Ie(r2,n)); n proved......
      eigen \e nInl(w,Ie(r2,n)); n
       use Eql_ie_cong; r1; r2; n
        use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Ie(r1,n); Ie(r2,n); w
         use Type_of_ie; r1; n
          use Type_of_ie; r2; n
           inst* \e nInl(w,Ie(r1,n)); n proved............

rem 
  \para \bf  Idempotentné vlastnosti  \end 

thm Eql_pe_rep
  Re(r) -> Eql(Pe(r,r),r)
proof 
 use Eql_def.0; Pe(r,r); r
  eigen* \a w(Inl(w,Pe(r,r)) <-> Inl(w,r)).0; w
   use Inl_pe.0; r; r; w proved....

rem 
  \para \bf  Vlastnosti identít  \end 

thm Eql_pe_ident_lt
  Re(r) -> Eql(Pe(Ze,r),r)
proof 
 use Eql_def.0; Pe(Ze,r); r
  eigen* \a w(Inl(w,Pe(Ze,r)) <-> Inl(w,r)).0; w
   use Inl_pe.0; Ze; r; w
    use Inl_ze.0; w proved.....

thm Eql_pe_ident_rt
  Re(r) -> Eql(Pe(r,Ze),r)
proof 
 use Eql_def.0; Pe(r,Ze); r
  eigen* \a w(Inl(w,Pe(r,Ze)) <-> Inl(w,r)).0; w
   use Inl_pe.0; r; Ze; w
    use Inl_ze.0; w proved.....

thm Eql_te_ident_rt
  Re(r) -> Eql(Te(r,Oe),r)
proof 
 use Eql_def.0; Te(r,Oe); r
  eigen* \a w(Inl(w,Te(r,Oe)) <-> Inl(w,r)).0; w
   use Inl_te.0; r; Oe; w
    split* \e w1(\e w2(w = w1++w2 & Inl(w2,Oe)) & Inl(w1,r)) <-> Inl(w,r).2,0,0
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Oe)) & Inl(w1,r)).0:0,3,0,1,0; w1,
                                                                          w2
      use Inl_oe.2,0,0; w2 proved..
     inst* \e w1(\e w2(w = w1++w2 & Inl(w2,Oe)) & Inl(w1,r)):0,3,0,1,0; w; 0
      use Inl_oe.2,1,0; 0 proved.......

thm Eql_te_ident_lt
  Re(r) -> Eql(Te(Oe,r),r)
proof 
 use Eql_def.0; Te(Oe,r); r
  eigen* \a w(Inl(w,Te(Oe,r)) <-> Inl(w,r)).0; w
   use Inl_te.0; Oe; r; w
    split* \e w1(\e w2(w = w1++w2 & Inl(w2,r)) & Inl(w1,Oe)) <-> Inl(w,r).2,0,0
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r)) & Inl(w1,Oe)).0:0,3,0,1,0; w1,
                                                                          w2
      use Inl_oe.2,0,0; w1 proved..
     inst* \e w1(\e w2(w = w1++w2 & Inl(w2,r)) & Inl(w1,Oe)):0,3,0,1,0; 0; w
      use Inl_oe.2,1,0; 0 proved.......

rem 
  \para \bf  Eliminačné vlastnosti  \end 

thm Eql_te_elim_rt
  Re(r) -> Eql(Te(r,Ze),Ze)
proof 
 use Eql_def.0; Te(r,Ze); Ze
  eigen* \a w(Inl(w,Te(r,Ze)) <-> Inl(w,Ze)).0; w
   use Inl_te.0; r; Ze; w
    split* \e w1(\e w2(w = w1++w2 & Inl(w2,Ze)) & Inl(w1,r)) <-> Inl(w,Ze).2,0,0
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Ze)) & Inl(w1,r)).0:0,3,0,1,0; w1,
                                                                          w2
      use Inl_ze.2,0,0; w2 proved..
     use Inl_ze.2,0,0; w proved......

thm Eql_te_elim_lt
  Re(r) -> Eql(Te(Ze,r),Ze)
proof 
 use Eql_def.0; Te(Ze,r); Ze
  eigen* \a w(Inl(w,Te(Ze,r)) <-> Inl(w,Ze)).0; w
   use Inl_te.0; Ze; r; w
    split* \e w1(\e w2(w = w1++w2 & Inl(w2,r)) & Inl(w1,Ze)) <-> Inl(w,Ze).2,0,0
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r)) & Inl(w1,Ze)).0:0,3,0,1,0; w1,
                                                                          w2
      use Inl_ze.2,0,0; w1 proved..
     use Inl_ze.2,0,0; w proved......

rem 
  \para \bf  Asociatívne vlastnosti  \end 

thm Eql_pe_assoc
  Re(r1) & Re(r2) & Re(r3) -> Eql(Pe(Pe(r1,r2),r3),Pe(r1,Pe(r2,r3)))
proof 
 use Eql_def.0; Pe(Pe(r1,r2),r3); Pe(r1,Pe(r2,r3))
  eigen* \a w(Inl(w,Pe(Pe(r1,r2),r3)) <-> Inl(w,Pe(r1,Pe(r2,r3)))).0; w
   use Inl_pe.0; r1; Pe(r2,r3); w
    use Inl_pe.0; Pe(r1,r2); r3; w
     use Inl_pe.0; r1; r2; w
      use Inl_pe.0; r2; r3; w proved.......

thm Eql_te_assoc
  Re(r1) & Re(r2) & Re(r3) -> Eql(Te(Te(r1,r2),r3),Te(r1,Te(r2,r3)))
proof 
 use Eql_def.0; Te(Te(r1,r2),r3); Te(r1,Te(r2,r3))
  eigen* \a w(Inl(w,Te(Te(r1,r2),r3)) <-> Inl(w,Te(r1,Te(r2,r3)))).0; w
   use Inl_te.0; r1; Te(r2,r3); w
    use Inl_te.0; Te(r1,r2); r3; w
     split* \e w1(\e w2(w = w1++w2 & Inl(w2,r3)) & Inl(w1,Te(r1,r2))) <-> 
            \e w1(\e w2(w = w1++w2 & Inl(w2,Te(r2,r3))) & Inl(w1,r1)).2,0,0
      eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r3)) & Inl(w1,Te(r1,r2))).0:0,3,0,
                                                                        1,0; abs,
                                                                             cs
       use Inl_te.1,0,2,0,0; r1; r2; abs
        eigen \e w1(\e w2(abs = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)).0:0,3,0,1,0; as,
                                                                                bs
         inst* \e w1(\e w2(as++bs++cs = w1++w2 & Inl(w2,Te(r2,r3))) & Inl(w1,r1)):0,
                                                                                  3,
                                                                                  0,
                                                                                  1,
                                                                                  0; as; bs++cs
          use Inl_te.0; r2; r3; bs++cs
           inst* \e w1(\e w2(bs++cs = w1++w2 & Inl(w2,r3)) & Inl(w1,r2)):0,3,0,1,
                                                                         0; bs; cs proved......
      eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Te(r2,r3))) & Inl(w1,r1)).0:0,3,0,
                                                                        1,0; as,
                                                                             bcs
       use Inl_te.1,0,2,0,0; r2; r3; bcs
        eigen \e w1(\e w2(bcs = w1++w2 & Inl(w2,r3)) & Inl(w1,r2)).0:0,3,0,1,0; bs,
                                                                                cs
         inst* \e w1(\e w2(as++bs++cs = w1++w2 & Inl(w2,r3)) & Inl(w1,Te(r1,r2))):0,
                                                                                  3,
                                                                                  0,
                                                                                  1,
                                                                                  0; as++bs; cs
          use Inl_te.0; r1; r2; as++bs
           inst* \e w1(\e w2(as++bs = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)):0,3,0,1,
                                                                         0; as; bs proved............

rem 
  \para \bf  Komutatívne vlastnosti  \end 

thm Eql_pe_comm
  Re(r1) & Re(r2) -> Eql(Pe(r1,r2),Pe(r2,r1))
proof 
 use Eql_def.0; Pe(r1,r2); Pe(r2,r1)
  eigen* \a w(Inl(w,Pe(r1,r2)) <-> Inl(w,Pe(r2,r1))).0; w
   use Inl_pe.0; r2; r1; w
    use Inl_pe.0; r1; r2; w proved.....

thm Eql_pe_comm3_lt
  Re(r1) & Re(r2) & Re(r3) -> Eql(Pe(r1,Pe(r2,r3)),Pe(r2,Pe(r1,r3)))
proof 
 use Eql_trans; Pe(r1,Pe(r2,r3)); Pe(Pe(r1,r2),r3); Pe(r2,Pe(r1,r3))
  split Eql(Pe(r1,Pe(r2,r3)),Pe(Pe(r1,r2),r3)) & 
        Eql(Pe(Pe(r1,r2),r3),Pe(r2,Pe(r1,r3))) -> 
        Eql(Pe(r1,Pe(r2,r3)),Pe(r2,Pe(r1,r3))).2,(4,1,1,0),0
   weak* Eql(Pe(r1,Pe(r2,r3)),Pe(r2,Pe(r1,r3)))
    use Eql_pe_assoc; r1; r2; r3
     use Eql_sym; Pe(Pe(r1,r2),r3); Pe(r1,Pe(r2,r3)) proved...
   weak* Eql(Pe(r1,Pe(r2,r3)),Pe(r2,Pe(r1,r3)))
    use Eql_trans; Pe(Pe(r1,r2),r3); Pe(Pe(r2,r1),r3); Pe(r2,Pe(r1,r3))
     split Eql(Pe(Pe(r1,r2),r3),Pe(Pe(r2,r1),r3)) & 
           Eql(Pe(Pe(r2,r1),r3),Pe(r2,Pe(r1,r3))) -> 
           Eql(Pe(Pe(r1,r2),r3),Pe(r2,Pe(r1,r3))).2,(4,1,1,0),0
      weak* Eql(Pe(Pe(r1,r2),r3),Pe(r2,Pe(r1,r3)))
       use Eql_pe_cong; Pe(r1,r2); r3; Pe(r2,r1); r3
        split Eql(Pe(r1,r2),Pe(r2,r1)) & Eql(r3,r3) -> 
              Eql(Pe(Pe(r1,r2),r3),Pe(Pe(r2,r1),r3)).2,(4,1,1,0),0
         weak* Eql(Pe(Pe(r1,r2),r3),Pe(Pe(r2,r1),r3))
          use Eql_pe_comm; r1; r2 proved..
         use Eql_refl; r3 proved.
         proved...
      weak* Eql(Pe(Pe(r1,r2),r3),Pe(r2,Pe(r1,r3)))
       use Eql_pe_assoc; r2; r1; r3 proved..
      proved...
   proved...

thm Eql_pe_comm3_rt
  Re(r1) & Re(r2) & Re(r3) -> Eql(Pe(r1,Pe(r2,r3)),Pe(r3,Pe(r2,r1)))
proof 
 use Eql_trans; Pe(r1,Pe(r2,r3)); Pe(r2,Pe(r1,r3)); Pe(r3,Pe(r2,r1))
  split Eql(Pe(r1,Pe(r2,r3)),Pe(r2,Pe(r1,r3))) & 
        Eql(Pe(r2,Pe(r1,r3)),Pe(r3,Pe(r2,r1))) -> 
        Eql(Pe(r1,Pe(r2,r3)),Pe(r3,Pe(r2,r1))).2,(4,1,1,0),0
   weak* Eql(Pe(r1,Pe(r2,r3)),Pe(r3,Pe(r2,r1)))
    use Eql_pe_comm3_lt; r1; r2; r3 proved..
   weak* Eql(Pe(r1,Pe(r2,r3)),Pe(r3,Pe(r2,r1)))
    use Eql_trans; Pe(r2,Pe(r1,r3)); Pe(r2,Pe(r3,r1)); Pe(r3,Pe(r2,r1))
     split Eql(Pe(r2,Pe(r1,r3)),Pe(r2,Pe(r3,r1))) & 
           Eql(Pe(r2,Pe(r3,r1)),Pe(r3,Pe(r2,r1))) -> 
           Eql(Pe(r2,Pe(r1,r3)),Pe(r3,Pe(r2,r1))).2,(4,1,1,0),0
      weak* Eql(Pe(r2,Pe(r1,r3)),Pe(r3,Pe(r2,r1)))
       use Eql_pe_cong; r2; Pe(r1,r3); r2; Pe(r3,r1)
        split Eql(r2,r2) & Eql(Pe(r1,r3),Pe(r3,r1)) -> 
              Eql(Pe(r2,Pe(r1,r3)),Pe(r2,Pe(r3,r1))).2,(4,1,1,0),0
         weak* Eql(Pe(r2,Pe(r1,r3)),Pe(r2,Pe(r3,r1)))
          use Eql_refl; r2 proved..
         weak* Eql(Pe(r2,Pe(r1,r3)),Pe(r2,Pe(r3,r1)))
          use Eql_pe_comm; r1; r3 proved..
         proved...
      weak* Eql(Pe(r2,Pe(r1,r3)),Pe(r3,Pe(r2,r1)))
       use Eql_pe_comm3_lt; r2; r3; r1 proved..
      proved...
   proved...

rem 
  \para \bf  Distributívne vlastnosti  \end 

thm Eql_dist_lt
  Re(r1) & Re(r2) & Re(r3) -> Eql(Te(r1,Pe(r2,r3)),Pe(Te(r1,r2),Te(r1,r3)))
proof 
 use Eql_def.0; Te(r1,Pe(r2,r3)); Pe(Te(r1,r2),Te(r1,r3))
  eigen* \a w(Inl(w,Te(r1,Pe(r2,r3))) <-> Inl(w,Pe(Te(r1,r2),Te(r1,r3)))).0; w
   use Inl_pe.0; Te(r1,r2); Te(r1,r3); w
    use Inl_te.0; r1; Pe(r2,r3); w
     use Inl_te.0; r1; r2; w
      use Inl_te.0; r1; r3; w
       split* \e w1(\e w2(w = w1++w2 & Inl(w2,Pe(r2,r3))) & Inl(w1,r1)) <-> 
              \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)) \/ 
              \e w1(\e w2(w = w1++w2 & Inl(w2,r3)) & Inl(w1,r1)).2,0,1,
                                                                 (4,0,0,0),0
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Pe(r2,r3))) & Inl(w1,r1)).0:0,3,
                                                                          0,1,0; w1,
                                                                                 w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r2)) & Inl(w3,r1)):0,3,0,1,0; w1; w2
          inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r3)) & Inl(w3,r1)):0,3,0,1,0; w1; w2
           use Inl_pe.0; r2; r3; w2
            split Inl(w2,r2) \/ Inl(w2,r3).4,0,0,0
             proved
             proved.....
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r2)) & Inl(w1,r1)).0:0,3,0,1,0; w1,
                                                                              w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,Pe(r2,r3))) & Inl(w3,r1)):0,
                                                                              3,
                                                                              0,
                                                                              1,0; w1; w2
          use Inl_pe.0; r2; r3; w2 proved...
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r3)) & Inl(w1,r1)).0:0,3,0,1,0; w1,
                                                                              w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,Pe(r2,r3))) & Inl(w3,r1)):0,
                                                                              3,
                                                                              0,
                                                                              1,0; w1; w2
          use Inl_pe.0; r2; r3; w2 proved...........

thm Eql_dist_rt
  Re(r1) & Re(r2) & Re(r3) -> Eql(Te(Pe(r2,r3),r1),Pe(Te(r2,r1),Te(r3,r1)))
proof 
 use Eql_def.0; Te(Pe(r2,r3),r1); Pe(Te(r2,r1),Te(r3,r1))
  eigen* \a w(Inl(w,Te(Pe(r2,r3),r1)) <-> Inl(w,Pe(Te(r2,r1),Te(r3,r1)))).0; w
   use Inl_pe.0; Te(r2,r1); Te(r3,r1); w
    use Inl_te.0; Pe(r2,r3); r1; w
     use Inl_te.0; r2; r1; w
      use Inl_te.0; r3; r1; w
       split* \e w1(\e w2(w = w1++w2 & Inl(w2,r1)) & Inl(w1,Pe(r2,r3))) <-> 
              \e w1(\e w2(w = w1++w2 & Inl(w2,r1)) & Inl(w1,r2)) \/ 
              \e w1(\e w2(w = w1++w2 & Inl(w2,r1)) & Inl(w1,r3)).2,0,1,
                                                                 (4,0,0,0),0
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r1)) & Inl(w1,Pe(r2,r3))).0:0,3,
                                                                          0,1,0; w1,
                                                                                 w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r1)) & Inl(w3,r2)):0,3,0,1,0; w1; w2
          inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r1)) & Inl(w3,r3)):0,3,0,1,0; w1; w2
           use Inl_pe.0; r2; r3; w1
            split Inl(w1,r2) \/ Inl(w1,r3).4,0,0,0
             proved
             proved.....
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r1)) & Inl(w1,r2)).0:0,3,0,1,0; w1,
                                                                              w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r1)) & Inl(w3,Pe(r2,r3))):0,
                                                                              3,
                                                                              0,
                                                                              1,0; w1; w2
          use Inl_pe.0; r2; r3; w1 proved...
        eigen \e w1(\e w2(w = w1++w2 & Inl(w2,r1)) & Inl(w1,r3)).0:0,3,0,1,0; w1,
                                                                              w2
         inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,r1)) & Inl(w3,Pe(r2,r3))):0,
                                                                              3,
                                                                              0,
                                                                              1,0; w1; w2
          use Inl_pe.0; r2; r3; w1 proved...........

rem 
  \para \bf  Kleeneho vlastnosti  \end 

lemma Eql_sete_ie
  Re(r) -> \e nInl(w,Te(r,Ie(r,n))) <-> Inl(w,Te(r,Se(r)))
proof 
 use Inl_te.0; r; Se(r); w
  split* \e nInl(w,Te(r,Ie(r,n))) <-> 
         \e w1(\e w2(w = w1++w2 & Inl(w2,Se(r))) & Inl(w1,r)).2,0,0
   eigen \e nInl(w,Te(r,Ie(r,n))); n
    use Type_of_ie; r; n
     use Inl_te.1,0,2,0,0; r; Ie(r,n); w
      eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Ie(r,n))) & Inl(w1,r)).0:0,3,0,1,0; w1,
                                                                                w2
       inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,Se(r))) & Inl(w3,r)):0,3,0,1,0; w1; w2
        use Inl_se_ie.1,0,2,1,0:0,2,1,2,0,1; r; w2; n proved......
   eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Se(r))) & Inl(w1,r)).0:0,3,0,1,0; w1,
                                                                           w2
    use Inl_se_ie.1,0,2,0,0; r; w2
     eigen \e nInl(w2,Ie(r,n)); n
      inst* \e nInl(w1++w2,Te(r,Ie(r,n))); n
       use Type_of_ie; r; n
        use Inl_te.1,0,2,1,0:0,2,1,2,0,1; r; Ie(r,n); w1++w2; w1; w2 proved.........

thm Eql_se_rec
  Re(r) -> Eql(Se(r),Pe(Oe,Te(r,Se(r))))
proof 
 use Eql_def.0; Se(r); Pe(Oe,Te(r,Se(r)))
  eigen* \a w(Inl(w,Se(r)) <-> Inl(w,Pe(Oe,Te(r,Se(r))))).0; w
   use Inl_se_ie.0; r; w
    cut* \e nInl(w,Ie(r,n)) <-> Inl(w,Oe) \/ \e nInl(w,Ie(r,n+1))
     weak* \e nInl(w,Ie(r,n)) <-> Inl(w,Pe(Oe,Te(r,Se(r))))
      split* \e nInl(w,Ie(r,n)) <-> Inl(w,Oe) \/ \e nInl(w,Te(r,Ie(r,n))).2,0,1,
                                                                          (4,0,
                                                                           0,0),
                                                                          0
       eigen \e nInl(w,Ie(r,n)); n
        case N; n @ 0; m
         proved
         inst* \e nInl(w,Te(r,Ie(r,n))); m proved...
       inst* \e nInl(w,Ie(r,n)); 0 proved.
       eigen \e nInl(w,Te(r,Ie(r,n))); n
        inst* \e nInl(w,Ie(r,n)); n+1 proved....
     use Eql_sete_ie.0; r; w
      use Inl_pe.0; Oe; Te(r,Se(r)); w proved.......

thm Eql_sete_ze_lt
  Re(r) -> Eql(Se Pe(Ze,r),Se(r))
proof 
 use Eql_se_cong; Pe(Ze,r); r
  use Eql_pe_ident_lt; r proved...

lemma Lemma_sete_lt
  \a w(Re(r) & Inl(w,Ie(Pe(Oe,r),n)) -> Inl(w,Se(r)))
proof 
 ind N; n @ 0; n
  eigen* \a w(Inl(w,Oe) -> Inl(w,Se(r))).0; w
   use Inl_se_ie.1,0,2,1,0:0,2,1,2,0,1; r; w; 0 proved..
  eigen* \a w(Inl(w,Te(Pe(Oe,r),Ie(Pe(Oe,r),n))) -> Inl(w,Se(r))).0; w
   use Type_of_ie; Pe(Oe,r); n
    use Inl_te.1,0,2,0,0; Pe(Oe,r); Ie(Pe(Oe,r),n); w
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Ie(Pe(Oe,r),n))) & Inl(w1,Pe(Oe,r))).0:0,
                                                                                  3,
                                                                                  0,
                                                                                  1,
                                                                                  0; w1,
                                                                                     w2
      inst \a w(Inl(w,Ie(Pe(Oe,r),n)) -> Inl(w,Se(r))); w2
       use Inl_pe.1,0,2,0,0; Oe; r; w1
        use Inl_oe.2,0,0; w1
         use Inl_te.1,0,2,1,0:0,2,1,2,0,1; r; Se(r); w; w1; w2
          use Inl_se_simp; r; w1++w2
           split Inl(w1,Oe) \/ Inl(w1,r).4,0,0,0
            proved
            proved............

lemma Lemma_sete_rt
  \a w(Re(r) & Inl(w,Ie(r,n)) -> Inl(w,Se Pe(Oe,r)))
proof 
 ind N; n @ 0; n
  eigen* \a w(Inl(w,Oe) -> Inl(w,Se Pe(Oe,r))).0; w
   use Inl_se_ie.1,0,2,1,0:0,2,1,2,0,1; Pe(Oe,r); w; 0 proved..
  eigen* \a w(Inl(w,Te(r,Ie(r,n))) -> Inl(w,Se Pe(Oe,r))).0; w
   use Inl_te.1,0,2,0,0; r; Ie(r,n); w
    use Type_of_ie; r; n
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Ie(r,n))) & Inl(w1,r)).0:0,3,0,1,0; w1,
                                                                               w2
      inst \a w(Inl(w,Ie(r,n)) -> Inl(w,Se Pe(Oe,r))); w2
       use Inl_pe.1,0,2,1,1,(4,1,0),0; Oe; r; w1
        use Inl_te.1,0,2,1,0:0,2,1,2,0,1; Pe(Oe,r); Se Pe(Oe,r); w; w1; w2
         use Inl_se_simp; Pe(Oe,r); w1++w2 proved..........

thm Eql_sete_oe
  Re(r) -> Eql(Se Pe(Oe,r),Se(r))
proof 
 use Eql_def.0; Se Pe(Oe,r); Se(r)
  eigen* \a w(Inl(w,Se Pe(Oe,r)) <-> Inl(w,Se(r))).0; w
   split* Inl(w,Se Pe(Oe,r)) <-> Inl(w,Se(r)).2,0,0
    use Inl_se_ie.1,0,2,0,0; Pe(Oe,r); w
     eigen \e nInl(w,Ie(Pe(Oe,r),n)); n
      use Lemma_sete_lt; r; n; w proved...
    use Inl_se_ie.1,0,2,0,0; r; w
     eigen \e nInl(w,Ie(r,n)); n
      use Lemma_sete_rt; r; n; w proved.......

rem 
  \para \bf  Vlastnosti zreťazenia zoznamov  \end 

thm Con_one
  Re(r) -> Inl(w,Con(r,0)) <-> Inl(w,r)
proof 
 use Eql_te_ident_rt; r
  use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Te(r,Oe); r; w proved...

thm Con_ze
  Lre(rs) -> Inl(w,Con(Ze,rs)) <-> Inl(w,Ze)
proof 
 use Eql_te_elim_lt; Con(rs)
  use Type_of_con; rs
   use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Te(Ze,Con(rs)); Ze; w proved....

thm Con_oe
  Lre(rs) -> Inl(w,Con(Oe,rs)) <-> Inl(w,Con(rs))
proof 
 use Inl_te.0; Oe; Con(rs); w
  use Type_of_con; rs
   split* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Oe)) <-> 
          Inl(w,Con(rs)).2,0,0
    eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Oe)).0:0,3,0,1,0; w1,
                                                                               w2
     use Inl_oe.2,0,0; w1 proved..
    inst* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Oe)):0,3,0,1,0; 0; w
     use Inl_oe.2,1,0; 0 proved......

thm Con_ce
  Lre(rs) -> Inl(w,Con(Ce(x),rs)) <-> \e w1(w = x,w1 & Inl(w1,Con(rs)))
proof 
 use Type_of_con; rs
  use Inl_te.0; Ce(x); Con(rs); w
   weak Inl(w,Te(Ce(x),Con(rs))) <-> 
        \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Ce(x)))
    cut* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Ce(x))) <-> 
         \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & w1 = x,0)
     weak* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Ce(x))) <-> 
           \e w1(w = x,w1 & Inl(w1,Con(rs)))
      split* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Ce(x))) <-> 
             \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & w1 = x,0).2,0,0
       eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Ce(x))).0:0,3,
                                                                          0,1,0; w1,
                                                                                 w2
        inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,Con(rs))) & w3 = x,0):0,3,0,1,
                                                                         0; w1; w2
         use Inl_ce.2,0,0; w1; x proved...
       eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & w1 = x,0).0:0,3,0,1,0; w1,
                                                                                w2
        inst* \e w1(\e w3(x,w2 = w1++w3 & Inl(w3,Con(rs))) & Inl(w1,Ce(x))):0,3,
                                                                            0,1,0; w1; w2
         use Inl_ce.2,1,0; x,0; x proved.....
     weak \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Ce(x))) <-> 
          \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & w1 = x,0)
      split* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & w1 = x,0) <-> 
             \e w1(w = x,w1 & Inl(w1,Con(rs))).2,0,0
       eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & w1 = x,0).0:0,3,0,1,0; w1,
                                                                                w2
        inst* \e w1(w2 = w1 & Inl(w1,Con(rs))); w2 proved..
       eigen \e w1(w = x,w1 & Inl(w1,Con(rs))).0; w1
        inst* \e w2(\e w3(x,w1 = w2++w3 & Inl(w3,Con(rs))) & w2 = x,0):0,3,0,1,0; x,0; w1 proved.........

thm Con_pe
  Re(r1) & Re(r2) & Lre(rs) -> Inl(w,Con(Pe(r1,r2),rs)) <-> 
  Inl(w,Con(r1,rs)) \/ Inl(w,Con(r2,rs))
proof 
 use Type_of_con; rs
  use Inl_te.0; Pe(r1,r2); Con(rs); w
   split* \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Pe(r1,r2))) <-> 
          Inl(w,Te(r1,Con(rs))) \/ Inl(w,Te(r2,Con(rs))).2,0,1,(4,0,0,0),0
    eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,Pe(r1,r2))).0:0,3,
                                                                           0,1,
                                                                           0; w1,
                                                                              w2
     use Inl_pe.1,0,2,0,0; r1; r2; w1
      use Inl_te.1,0,2,1,0:0,2,1,2,0,1; r1; Con(rs); w1++w2; w1; w2
       use Inl_te.1,0,2,1,0:0,2,1,2,0,1; r2; Con(rs); w1++w2; w1; w2
        split Inl(w1,r1) \/ Inl(w1,r2).4,0,0,0
         proved
         proved.....
    use Inl_te.1,0,2,0,0; r1; Con(rs); w
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,r1)).0:0,3,0,1,0; w1,
                                                                                w2
      inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,Con(rs))) & Inl(w3,Pe(r1,r2))):0,
                                                                                3,
                                                                                0,
                                                                                1,
                                                                                0; w1; w2
       use Inl_pe.1,0,2,1,1,(4,0,0),0; r1; r2; w1 proved....
    use Inl_te.1,0,2,0,0; r2; Con(rs); w
     eigen \e w1(\e w2(w = w1++w2 & Inl(w2,Con(rs))) & Inl(w1,r2)).0:0,3,0,1,0; w1,
                                                                                w2
      inst* \e w3(\e w4(w1++w2 = w3++w4 & Inl(w4,Con(rs))) & Inl(w3,Pe(r1,r2))):0,
                                                                                3,
                                                                                0,
                                                                                1,
                                                                                0; w1; w2
       use Inl_pe.1,0,2,1,1,(4,1,0),0; r1; r2; w1 proved........

thm Con_te
  Re(r1) & Re(r2) & Lre(rs) -> Inl(w,Con(Te(r1,r2),rs)) <-> Inl(w,Con(r1,r2,rs))
proof 
 use Eql_te_assoc; r1; r2; Con(rs)
  use Type_of_con; rs
   use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Te(Te(r1,r2),Con(rs)); Te(r1,Te(r2,Con(rs))); w proved....

thm Con_se
  Re(r) & Lre(rs) -> Inl(w,Con(Se(r),rs)) <-> 
  Inl(w,Con(rs)) \/ Inl(w,Con(r,Se(r),rs))
proof 
 use Type_of_con; rs
  cut* Eql(Te(Se(r),Con(rs)),Pe(Con(rs),Te(r,Te(Se(r),Con(rs)))))
   weak* Inl(w,Te(Se(r),Con(rs))) <-> 
         Inl(w,Con(rs)) \/ Inl(w,Te(r,Te(Se(r),Con(rs))))
    use Eql_trans; Te(Se(r),Con(rs)); Te(Pe(Oe,Te(r,Se(r))),Con(rs)); Pe(Con(rs),Te(r,Te(Se(r),Con(rs))))
     split Eql(Te(Se(r),Con(rs)),Te(Pe(Oe,Te(r,Se(r))),Con(rs))) & 
           Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
               Pe(Con(rs),Te(r,Te(Se(r),Con(rs))))) -> 
           Eql(Te(Se(r),Con(rs)),Pe(Con(rs),Te(r,Te(Se(r),Con(rs))))).2,
                                                                      (4,1,1,0),
                                                                      0
      weak* Eql(Te(Se(r),Con(rs)),Pe(Con(rs),Te(r,Te(Se(r),Con(rs)))))
       use Eql_se_rec; r
        use Eql_refl; Con(rs)
         use Eql_te_cong; Se(r); Con(rs); Pe(Oe,Te(r,Se(r))); Con(rs) proved....
      weak* Eql(Te(Se(r),Con(rs)),Pe(Con(rs),Te(r,Te(Se(r),Con(rs)))))
       use Eql_trans; Te(Pe(Oe,Te(r,Se(r))),Con(rs)); Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs)))); Pe(Con(rs),Te(r,Te(Se(r),Con(rs))))
        split Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                  Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs))))) & 
              Eql(Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs)))),
                  Pe(Con(rs),Te(r,Te(Se(r),Con(rs))))) -> 
              Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                  Pe(Con(rs),Te(r,Te(Se(r),Con(rs))))).2,(4,1,1,0),0
         weak* Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                   Pe(Con(rs),Te(r,Te(Se(r),Con(rs)))))
          use Eql_trans; Te(Pe(Oe,Te(r,Se(r))),Con(rs)); Pe(Te(Oe,Con(rs)),Te(Te(r,Se(r)),Con(rs))); Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs))))
           split Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                     Pe(Te(Oe,Con(rs)),Te(Te(r,Se(r)),Con(rs)))) & 
                 Eql(Pe(Te(Oe,Con(rs)),Te(Te(r,Se(r)),Con(rs))),
                     Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs))))) -> 
                 Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                     Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs))))).2,(4,1,1,0),0
            weak* Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                      Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs)))))
             use Eql_dist_rt; Con(rs); Oe; Te(r,Se(r)) proved..
            weak* Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                      Pe(Te(Oe,Con(rs)),Te(r,Te(Se(r),Con(rs)))))
             use Eql_refl; Te(Oe,Con(rs))
              use Eql_te_assoc; r; Se(r); Con(rs)
               use Eql_pe_cong; Te(Oe,Con(rs)); Te(Te(r,Se(r)),Con(rs)); Te(Oe,Con(rs)); Te(r,Te(Se(r),Con(rs))) proved....
            proved...
         weak* Eql(Te(Pe(Oe,Te(r,Se(r))),Con(rs)),
                   Pe(Con(rs),Te(r,Te(Se(r),Con(rs)))))
          use Eql_refl; Te(r,Te(Se(r),Con(rs)))
           use Eql_te_ident_lt; Con(rs)
            use Eql_pe_cong; Te(Oe,Con(rs)); Te(r,Te(Se(r),Con(rs))); Con(rs); Te(r,Te(Se(r),Con(rs))) proved....
         proved...
      proved...
   use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Te(Se(r),Con(rs)); Pe(Con(rs),Te(r,Te(Se(r),Con(rs)))); w
    use Inl_pe.0; Con(rs); Te(r,Te(Se(r),Con(rs))); w proved.....

