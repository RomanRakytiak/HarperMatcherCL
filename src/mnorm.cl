mod Mnorm logic: 'cl'

incl Mtex

incl Maux

incl Msyntax

incl Mdebug

incl Msemantics

rem 
  \para \bf  Normalizácia regulárnych výrazov  \end 

rem 
  \para \bf  Normalizovaný regulárny výraz  \end 

rem 
  \para Normalizovaný regulárny výraz je regulárny výraz, ktorý neobsahuje 
  žiaden podvýraz pod Kleeneho hviezdičkou akceptujúci prázdne slovo. 

pred Nre 
  Nre(r) <-> Re(r) & \a s(Re(s) & Sub(Se(s),r) -> ~Inl(0,s))

thm Nre_def
  Nre(r) <-> Re(r) & \a s(Re(s) & Sub(Se(s),r) -> ~Inl(0,s))
proof 
 exp Nre; r proved..

rem 
  \para \bf  Vlastnosti normalizovaného regulárneho výrazu  \end 

thm Nre_re
  Nre(r) -> Re(r)
proof 
 use Nre_def.2,0,1,0,4,0,0; r proved..

thm Nre_ze
  Nre(Ze)
proof 
 use Nre_def.0; Ze proved..

thm Nre_oe
  Nre(Oe)
proof 
 use Nre_def.0; Oe proved..

thm Nre_ce
  Nre Ce(x)
proof 
 use Nre_def.0; Ce(x) proved..

thm Nre_pe
  Nre Pe(r1,r2) <-> Nre(r1) & Nre(r2)
proof 
 use Nre_def.0; Pe(r1,r2)
  use Nre_def.0; r1
   use Nre_def.0; r2
    split* Re(r1) & Re(r2) & \a s(Re(s) & Sub(Se(s),Pe(r1,r2)) -> ~Inl(0,s)) <-> 
           Re(r1) & \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)) & Re(r2) & 
           \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)).2,0,0
     split* \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)) & 
            \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)).4,0,0,0
      eigen* \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)).0; s
       inst \a s(Re(s) & Sub(Se(s),Pe(r1,r2)) -> ~Inl(0,s)); s proved..
      eigen* \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)).0; s
       inst \a s(Re(s) & Sub(Se(s),Pe(r1,r2)) -> ~Inl(0,s)); s
        cut Sub(Se(s),r1)
         proved
         proved....
     eigen* \a s(Re(s) & Sub(Se(s),Pe(r1,r2)) -> ~Inl(0,s)).0; s
      inst \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)); s
       inst \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)); s
        cut Sub(Se(s),r1)
         proved
         proved.........

thm Nre_te
  Nre Te(r1,r2) <-> Nre(r1) & Nre(r2)
proof 
 use Nre_def.0; Te(r1,r2)
  use Nre_def.0; r1
   use Nre_def.0; r2
    split* Re(r1) & Re(r2) & \a s(Re(s) & Sub(Se(s),Te(r1,r2)) -> ~Inl(0,s)) <-> 
           Re(r1) & \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)) & Re(r2) & 
           \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)).2,0,0
     split* \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)) & 
            \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)).4,0,0,0
      eigen* \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)).0; s
       inst \a s(Re(s) & Sub(Se(s),Te(r1,r2)) -> ~Inl(0,s)); s proved..
      eigen* \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)).0; s
       inst \a s(Re(s) & Sub(Se(s),Te(r1,r2)) -> ~Inl(0,s)); s
        cut Sub(Se(s),r1)
         proved
         proved....
     eigen* \a s(Re(s) & Sub(Se(s),Te(r1,r2)) -> ~Inl(0,s)).0; s
      inst \a s(Re(s) & Sub(Se(s),r1) -> ~Inl(0,s)); s
       inst \a s(Re(s) & Sub(Se(s),r2) -> ~Inl(0,s)); s
        cut Sub(Se(s),r1)
         proved
         proved.........

thm Nre_se
  Nre Se(r) <-> Nre(r) & ~Inl(0,r)
proof 
 use Nre_def.0; Se(r)
  use Nre_def.0; r
   split* Re(r) & \a s(Re(s) & Sub(Se(s),Se(r)) -> ~Inl(0,s)) <-> 
          Re(r) & \a s(Re(s) & Sub(Se(s),r) -> ~Inl(0,s)) & ~Inl(0,r).2,0,0
    eigen* \a s(Re(s) & Sub(Se(s),r) -> ~Inl(0,s)) & ~Inl(0,r).0:3,0,1,0; s
     split* (Re(s) & Sub(Se(s),r) -> ~Inl(0,s)) & ~Inl(0,r).4,0,0,0
      inst \a s(Re(s) & Sub(Se(s),Se(r)) -> ~Inl(0,s)); s
       cut r = s
        proved
        proved..
      inst \a s(Re(s) & Sub(Se(s),Se(r)) -> ~Inl(0,s)); r proved...
    eigen* \a s(Re(s) & Sub(Se(s),Se(r)) -> ~Inl(0,s)).0; s
     inst \a s(Re(s) & Sub(Se(s),r) -> ~Inl(0,s)); s
      cut r = s
       proved
       proved.......

rem 
  \para Predikát pre zoznam normalizovaných výrazov 

pred Lnre 
  Lnre(0)
  Lnre(r,rs) <- Nre(r) & Lnre(rs)

thm Type_of_lnre
  Lnre(rs) -> Lre(rs)
proof 
 ind Ln; rs @ 0; v,w
  proved
  use Nre_def.2,0,1,0,4,0,0; v proved...

rem 
  \para \bf  Boolovské operácie nad regulárnymi výrazmi  \end 

fun/2 Eor 'Tex_f2_eor'
  Eor(r1,r2) = Oe <- r1 = Oe
  Eor(r1,r2) = Oe <- r1 != Oe & r2 = Oe
  Eor(r1,r2) = Ze <- r1 != Oe & r2 != Oe

thm Type_of_eor
  Re Eor(r1,r2)
proof 
 cut r1 = Oe
  proved
  cut r2 = Oe
   proved
   proved...

thm Ret_of_eor
  Eor(r1,r2) = Oe \/ Eor(r1,r2) = Ze
proof 
 cut r1 = Oe
  proved
  cut r2 = Oe
   proved
   proved...

thm Eor_is_oe
  Eor(r1,r2) = Oe <-> r1 = Oe \/ r2 = Oe
proof 
 cut r1 = Oe
  proved
  cut r2 = Oe
   proved
   proved...

fun/2 Eand 'Tex_f2_eand'
  Eand(r1,r2) = Ze <- r1 = Ze
  Eand(r1,r2) = Ze <- r1 != Ze & r2 = Ze
  Eand(r1,r2) = Oe <- r1 != Ze & r2 != Ze

thm Type_of_eand
  Re Eand(r1,r2)
proof 
 cut r1 = Ze
  proved
  cut r2 = Ze
   proved
   proved...

thm Ret_of_eand
  Eand(r1,r2) = Oe \/ Eand(r1,r2) = Ze
proof 
 cut r1 = Ze
  proved
  cut r2 = Ze
   proved
   proved...

thm Eand_is_oe
  Eand(r1,r2) = Oe <-> r1 != Ze & r2 != Ze
proof 
 cut r1 = Ze
  proved
  cut r2 = Ze
   proved
   proved...

rem 
  \para \bf  Delta funkcia  \end 

fun Dt 'Tex_f1_re_dt'
  Dt(Ze) = Ze
  Dt(Oe) = Oe
  Dt Ce(x) = Ze
  Dt Pe(r1,r2) = Eor(Dt(r1),Dt(r2))
  Dt Te(r1,r2) = Eand(Dt(r1),Dt(r2))
  Dt Se(r) = Oe

thm Ret_of_dt
  Re(r) -> Dt(r) = Oe \/ Dt(r) = Ze
proof 
 case Re; r @ 0; 0; x; r1,r2; r1,r2; r1
  proved
  proved
  proved
  use Ret_of_eor; Dt(r1); Dt(r2)
   split Eor(Dt(r1),Dt(r2)) = Oe \/ Eor(Dt(r1),Dt(r2)) = Ze.4,0,0,0
    proved
    proved..
  use Ret_of_eand; Dt(r1); Dt(r2)
   split Eand(Dt(r1),Dt(r2)) = Oe \/ Eand(Dt(r1),Dt(r2)) = Ze.4,0,0,0
    proved
    proved..
  proved..

thm Type_of_dt
  Re(r) -> Re Dt(r)
proof 
 use Ret_of_dt; r
  split Dt(r) = Oe \/ Dt(r) = Ze.4,0,0,0
   proved
   proved...

thm Eql_dt_eand
  Re(r1) & Re(r2) -> Eql(Te(Dt(r1),Dt(r2)),Eand(Dt(r1),Dt(r2)))
proof 
 use Ret_of_dt; r1
  use Ret_of_dt; r2
   use Type_of_dt; r1
    use Type_of_dt; r2
     split Dt(r1) = Oe \/ Dt(r1) = Ze.4,0,0,0
      split Dt(r2) = Oe \/ Dt(r2) = Ze.4,0,0,0
       use Eql_te_ident_lt; Oe proved.
       use Eql_te_elim_rt; Oe proved..
      use Eql_te_elim_lt; Dt(r2) proved.......

thm Eql_dt_eor
  Re(r1) & Re(r2) -> Eql(Pe(Dt(r1),Dt(r2)),Eor(Dt(r1),Dt(r2)))
proof 
 use Ret_of_dt; r1
  use Ret_of_dt; r2
   split Dt(r1) = Oe \/ Dt(r1) = Ze.4,0,0,0
    split Dt(r2) = Oe \/ Dt(r2) = Ze.4,0,0,0
     use Eql_pe_rep; Oe proved.
     use Eql_pe_ident_rt; Oe proved..
    split Dt(r2) = Oe \/ Dt(r2) = Ze.4,0,0,0
     use Eql_pe_ident_lt; Oe proved.
     use Eql_pe_ident_lt; Ze proved......

thm Eql_sepe_ident_dt_lt
  Re(r1) & Re(r2) -> Eql(Se Pe(Dt(r2),r1),Se(r1))
proof 
 use Type_of_dt; r2
  use Ret_of_dt; r2
   use Eql_sete_ze_lt; r1
    use Eql_sete_oe; r1
     split Dt(r2) = Oe \/ Dt(r2) = Ze.4,0,0,0
      proved
      proved......

thm Nre_dt
  Re(r) -> Nre Dt(r)
proof 
 use Ret_of_dt; r
  use Nre_ze
   use Nre_oe
    split Dt(r) = Oe \/ Dt(r) = Ze.4,0,0,0
     proved
     proved.....

rem 
  \para \bf  Regulárny výraz bez prázdneho slova  \end 

fun De 'Tex_f1_re_de'
  De(Ze) = Ze
  De(Oe) = Ze
  De Ce(x) = Ce(x)
  De Pe(r1,r2) = Pe(De(r1),De(r2))
  De Te(r1,r2) = Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2)))
  De Se(r) = Te(De(r),Se De(r))

thm Type_of_de
  Re(r) -> Re De(r)
proof 
 ind* Re; r @ 0; 0; x; r1,r2; r1,r2; r
  proved
  proved
  proved
  proved
  use Type_of_dt; r1
   use Type_of_dt; r2 proved..
  proved..

thm De_not_empty
  Re(r) -> ~Inl(0,De(r))
proof 
 use Type_of_de; r
  ind Re; r @ 0; 0; x; r1,r2; r1,r2; r
   use Inl_ze.0; 0 proved.
   use Inl_ze.0; 0 proved.
   use Inl_ce.0; 0; x proved.
   use Inl_not_pe.1,0,2,1,0; De(r1); De(r2); 0 proved.
   use Inl_not_te.1,0,2,1,1,(4,0,0),0; De(r1); De(r2)
    use Inl_not_te.1,0,2,1,1,(4,0,0),0; De(r1); Dt(r2)
     use Inl_not_te.1,0,2,1,1,(4,1,0),0; Dt(r1); De(r2)
      use Inl_not_pe.1,0,2,1,0; Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))); Te(De(r1),De(r2)); 0
       use Inl_not_pe.1,0,2,1,0; Te(Dt(r1),De(r2)); Te(De(r1),Dt(r2)); 0 proved.....
   use Inl_not_te.1,0,2,1,1,(4,0,0),0; De(r); Se De(r) proved....

thm Nre_de
  Re(r) -> Nre De(r)
proof 
 ind* Re; r @ 0; 0; x; r1,r2; r1,r2; r
  use Nre_ze proved.
  use Nre_ze proved.
  use Nre_ce; x proved.
  use Nre_pe.2,1,0; De(r1); De(r2) proved.
  use Nre_dt; r1
   use Nre_dt; r2
    use Nre_te.2,1,0; Dt(r1); De(r2)
     use Nre_te.2,1,0; De(r1); Dt(r2)
      use Nre_te.2,1,0; De(r1); De(r2)
       use Nre_pe.2,1,0; Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))); Te(De(r1),De(r2))
        use Nre_pe.2,1,0; Te(Dt(r1),De(r2)); Te(De(r1),Dt(r2)) proved.......
  use De_not_empty; r
   use Nre_se.2,1,0; De(r)
    use Nre_te.2,1,0; De(r); Se De(r) proved.....

rem 
  \para \bf  Normalizačná funkcia  \end 

fun Norm 
  Norm(r) = Pe(Dt(r),De(r)) <- Guard

thm Norm_def
  Norm(r) = Pe(Dt(r),De(r))
proof 
 cut Guard
  proved
  exp Guard proved...

thm Type_of_norm
  Re(r) -> Re Norm(r)
proof 
 use Norm_def; r
  use Type_of_dt; r
   use Type_of_de; r proved....

rem 
  \para \bf  Normalizácia zachováva jazyk regulárneho výrazu  \end 

lemma Eql_pe_swap4
  Re(r1) & Re(r2) & Re(r3) & Re(r4) -> 
  Eql(Pe(Pe(r1,r2),Pe(r3,r4)),Pe(Pe(r1,r3),Pe(r2,r4)))
proof 
 use Eql_trans; Pe(Pe(r1,r2),Pe(r3,r4)); Pe(r1,Pe(r2,Pe(r3,r4))); Pe(Pe(r1,r3),Pe(r2,r4))
  split Eql(Pe(Pe(r1,r2),Pe(r3,r4)),Pe(r1,Pe(r2,Pe(r3,r4)))) & 
        Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(Pe(r1,r3),Pe(r2,r4))) -> 
        Eql(Pe(Pe(r1,r2),Pe(r3,r4)),Pe(Pe(r1,r3),Pe(r2,r4))).2,(4,1,1,0),0
   weak* Eql(Pe(Pe(r1,r2),Pe(r3,r4)),Pe(Pe(r1,r3),Pe(r2,r4)))
    use Eql_pe_assoc; r1; r2; Pe(r3,r4) proved..
   weak* Eql(Pe(Pe(r1,r2),Pe(r3,r4)),Pe(Pe(r1,r3),Pe(r2,r4)))
    use Eql_trans; Pe(r1,Pe(r2,Pe(r3,r4))); Pe(r1,Pe(r3,Pe(r2,r4))); Pe(Pe(r1,r3),Pe(r2,r4))
     split Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(r1,Pe(r3,Pe(r2,r4)))) & 
           Eql(Pe(r1,Pe(r3,Pe(r2,r4))),Pe(Pe(r1,r3),Pe(r2,r4))) -> 
           Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(Pe(r1,r3),Pe(r2,r4))).2,(4,1,1,0),0
      weak* Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(Pe(r1,r3),Pe(r2,r4)))
       use Eql_pe_cong; r1; Pe(r2,Pe(r3,r4)); r1; Pe(r3,Pe(r2,r4))
        split Eql(r1,r1) & Eql(Pe(r2,Pe(r3,r4)),Pe(r3,Pe(r2,r4))) -> 
              Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(r1,Pe(r3,Pe(r2,r4)))).2,(4,1,1,0),0
         use Eql_refl; r1 proved.
         weak* Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(r1,Pe(r3,Pe(r2,r4))))
          use Eql_pe_comm3_lt; r2; r3; r4 proved..
         proved...
      weak* Eql(Pe(r1,Pe(r2,Pe(r3,r4))),Pe(Pe(r1,r3),Pe(r2,r4)))
       use Eql_pe_assoc; r1; r3; Pe(r2,r4)
        use Eql_sym; Pe(Pe(r1,r3),Pe(r2,r4)); Pe(r1,Pe(r3,Pe(r2,r4))) proved...
      proved...
   proved...

lemma Eql_norm_pe
  Re(r1) & Re(r2) -> Eql(Norm Pe(r1,r2),Pe(Norm(r1),Norm(r2)))
proof 
 use Norm_def; Pe(r1,r2)
  use Norm_def; r1
   use Norm_def; r2
    use Type_of_de; r1
     use Type_of_de; r2
      use Type_of_dt; r1
       use Type_of_dt; r2
        use Type_of_eor; Dt(r1); Dt(r2)
         use Eql_trans; Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))); Pe(Pe(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))); Pe(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2)))
          split Eql(Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                    Pe(Pe(Dt(r1),Dt(r2)),Pe(De(r1),De(r2)))) & 
                Eql(Pe(Pe(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                    Pe(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2)))) -> 
                Eql(Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                    Pe(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2)))).2,(4,1,1,0),0
           weak* Eql(Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                     Pe(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2))))
            use Eql_refl; Pe(De(r1),De(r2))
             use Eql_pe_cong; Eor(Dt(r1),Dt(r2)); Pe(De(r1),De(r2)); Pe(Dt(r1),Dt(r2)); Pe(De(r1),De(r2))
              split Eql(Eor(Dt(r1),Dt(r2)),Pe(Dt(r1),Dt(r2))) -> 
                    Eql(Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                        Pe(Pe(Dt(r1),Dt(r2)),Pe(De(r1),De(r2)))).2,1,0
               weak* Eql(Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                         Pe(Pe(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))))
                use Eql_dt_eor; r1; r2
                 use Eql_sym; Pe(Dt(r1),Dt(r2)); Eor(Dt(r1),Dt(r2)) proved...
               proved....
           weak* Eql(Pe(Eor(Dt(r1),Dt(r2)),Pe(De(r1),De(r2))),
                     Pe(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2))))
            use Eql_pe_swap4; Dt(r1); Dt(r2); De(r1); De(r2) proved..
           proved...........

lemma Eql_te_pe_dist4
  Re(r1) & Re(r2) & Re(r3) & Re(r4) -> 
  Eql(Te(Pe(r1,r2),Pe(r3,r4)),
      Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
proof 
 use Eql_trans; Te(Pe(r1,r2),Pe(r3,r4)); Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)); Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
  split Eql(Te(Pe(r1,r2),Pe(r3,r4)),Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4))) & 
        Eql(Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)),
            Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))) -> 
        Eql(Te(Pe(r1,r2),Pe(r3,r4)),
            Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))).2,(4,1,1,0),0
   weak* Eql(Te(Pe(r1,r2),Pe(r3,r4)),
             Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
    use Eql_dist_lt; Pe(r1,r2); r3; r4 proved..
   weak* Eql(Te(Pe(r1,r2),Pe(r3,r4)),
             Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
    use Eql_trans; Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)); Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))); Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
     split Eql(Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)),
               Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4)))) & 
           Eql(Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))),
               Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))) -> 
           Eql(Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)),
               Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))).2,(4,1,1,0),
                                                                    0
      weak* Eql(Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)),
                Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
       use Eql_dist_rt; r3; r1; r2
        use Eql_dist_rt; r4; r1; r2
         use Eql_pe_cong; Te(Pe(r1,r2),r3); Te(Pe(r1,r2),r4); Pe(Te(r1,r3),Te(r2,r3)); Pe(Te(r1,r4),Te(r2,r4)) proved....
      weak* Eql(Pe(Te(Pe(r1,r2),r3),Te(Pe(r1,r2),r4)),
                Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
       use Eql_trans; Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))); Pe(Te(r1,r3),Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4)))); Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
        split Eql(Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))),
                  Pe(Te(r1,r3),Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))))) & 
              Eql(Pe(Te(r1,r3),Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4)))),
                  Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))) -> 
              Eql(Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))),
                  Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))).2,
                                                                       (4,1,1,0),
                                                                       0
         weak* Eql(Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))),
                   Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
          use Eql_pe_assoc; Te(r1,r3); Te(r2,r3); Pe(Te(r1,r4),Te(r2,r4)) proved..
         weak* Eql(Pe(Pe(Te(r1,r3),Te(r2,r3)),Pe(Te(r1,r4),Te(r2,r4))),
                   Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
          use Eql_pe_cong; Te(r1,r3); Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))); Te(r1,r3); Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))
           split Eql(Te(r1,r3),Te(r1,r3)) & 
                 Eql(Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))),
                     Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))) -> 
                 Eql(Pe(Te(r1,r3),Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4)))),
                     Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))).2,
                                                                          (4,1,
                                                                           1,0),
                                                                          0
            weak* Eql(Pe(Te(r1,r3),Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4)))),
                      Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
             use Eql_refl; Te(r1,r3) proved..
            weak* Eql(Pe(Te(r1,r3),Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4)))),
                      Pe(Te(r1,r3),Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))))
             use Eql_trans; Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))); Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4)); Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))
              split Eql(Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))),
                        Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4))) & 
                    Eql(Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4)),
                        Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))) -> 
                    Eql(Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))),
                        Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))).2,(4,1,1,0),0
               weak* Eql(Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))),
                         Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
                use Eql_pe_assoc; Te(r2,r3); Te(r1,r4); Te(r2,r4)
                 use Eql_sym; Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4)); Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))) proved...
               weak* Eql(Pe(Te(r2,r3),Pe(Te(r1,r4),Te(r2,r4))),
                         Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
                use Eql_pe_cong; Pe(Te(r2,r3),Te(r1,r4)); Te(r2,r4); Pe(Te(r1,r4),Te(r2,r3)); Te(r2,r4)
                 split Eql(Pe(Te(r2,r3),Te(r1,r4)),Pe(Te(r1,r4),Te(r2,r3))) & 
                       Eql(Te(r2,r4),Te(r2,r4)) -> 
                       Eql(Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4)),
                           Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4))).2,(4,1,1,0),0
                  weak* Eql(Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4)),
                            Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
                   use Eql_pe_comm; Te(r2,r3); Te(r1,r4) proved..
                  weak* Eql(Pe(Pe(Te(r2,r3),Te(r1,r4)),Te(r2,r4)),
                            Pe(Pe(Te(r1,r4),Te(r2,r3)),Te(r2,r4)))
                   use Eql_refl; Te(r2,r4) proved..
                  proved...
               proved...
            proved...
         proved...
      proved...
   proved...

lemma Eql_norm_te
  Re(r1) & Re(r2) -> Eql(Norm Te(r1,r2),Te(Norm(r1),Norm(r2)))
proof 
 use Norm_def; Te(r1,r2)
  use Norm_def; r1
   use Norm_def; r2
    use Type_of_dt; r1
     use Type_of_dt; r2
      use Type_of_de; r1
       use Type_of_de; r2
        use Type_of_eand; Dt(r1); Dt(r2)
         use Eql_trans; Pe(Eand(Dt(r1),Dt(r2)),
                           Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2)))); Pe(Te(Dt(r1),Dt(r2)),
                                                                                              Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2)))); Te(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2)))
          split Eql(Pe(Eand(Dt(r1),Dt(r2)),
                       Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                          Te(De(r1),De(r2)))),
                    Pe(Te(Dt(r1),Dt(r2)),
                       Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                          Te(De(r1),De(r2))))) & 
                Eql(Pe(Te(Dt(r1),Dt(r2)),
                       Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                          Te(De(r1),De(r2)))),
                    Te(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2)))) -> 
                Eql(Pe(Eand(Dt(r1),Dt(r2)),
                       Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                          Te(De(r1),De(r2)))),
                    Te(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2)))).2,(4,1,1,0),0
           weak* Eql(Pe(Eand(Dt(r1),Dt(r2)),
                        Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                           Te(De(r1),De(r2)))),
                     Te(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2))))
            use Eql_pe_cong; Eand(Dt(r1),Dt(r2)); Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2))); Te(Dt(r1),Dt(r2)); Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2)))
             split Eql(Eand(Dt(r1),Dt(r2)),Te(Dt(r1),Dt(r2))) & 
                   Eql(Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                          Te(De(r1),De(r2))),
                       Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                          Te(De(r1),De(r2)))) -> 
                   Eql(Pe(Eand(Dt(r1),Dt(r2)),
                          Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                             Te(De(r1),De(r2)))),
                       Pe(Te(Dt(r1),Dt(r2)),
                          Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                             Te(De(r1),De(r2))))).2,(4,1,1,0),0
              weak* Eql(Pe(Eand(Dt(r1),Dt(r2)),
                           Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                              Te(De(r1),De(r2)))),
                        Pe(Te(Dt(r1),Dt(r2)),
                           Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                              Te(De(r1),De(r2)))))
               use Eql_dt_eand; r1; r2
                use Eql_sym; Te(Dt(r1),Dt(r2)); Eand(Dt(r1),Dt(r2)) proved...
              weak* Eql(Pe(Eand(Dt(r1),Dt(r2)),
                           Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                              Te(De(r1),De(r2)))),
                        Pe(Te(Dt(r1),Dt(r2)),
                           Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                              Te(De(r1),De(r2)))))
               use Eql_refl; Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2))) proved..
              proved...
           weak* Eql(Pe(Eand(Dt(r1),Dt(r2)),
                        Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),
                           Te(De(r1),De(r2)))),
                     Te(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2))))
            use Eql_te_pe_dist4; Dt(r1); De(r1); Dt(r2); De(r2)
             use Eql_sym; Te(Pe(Dt(r1),De(r1)),Pe(Dt(r2),De(r2))); Pe(Te(Dt(r1),Dt(r2)),
                                                                      Pe(Pe(Te(Dt(r1),De(r2)),Te(De(r1),Dt(r2))),Te(De(r1),De(r2)))) proved...
           proved...........

lemma Eql_norm_se
  Re(r) -> Eql(Norm Se(r),Se Norm(r))
proof 
 use Type_of_norm; Se(r)
  use Type_of_norm; r
   use Norm_def; Se(r)
    use Norm_def; r
     use Eql_trans; Pe(Oe,Te(De(r),Se De(r))); Se De(r); Se Pe(Dt(r),De(r))
      split Eql(Pe(Oe,Te(De(r),Se De(r))),Se De(r)) & 
            Eql(Se De(r),Se Pe(Dt(r),De(r))) -> 
            Eql(Pe(Oe,Te(De(r),Se De(r))),Se Pe(Dt(r),De(r))).2,(4,1,1,0),0
       weak* Eql(Pe(Oe,Te(De(r),Se De(r))),Se Pe(Dt(r),De(r)))
        use Eql_se_rec; De(r)
         use Eql_sym; Se De(r); Pe(Oe,Te(De(r),Se De(r))) proved...
       weak* Eql(Pe(Oe,Te(De(r),Se De(r))),Se Pe(Dt(r),De(r)))
        use Eql_sepe_ident_dt_lt; De(r); r
         use Eql_sym; Se Pe(Dt(r),De(r)); Se De(r) proved...
       proved.......

thm Norm_ok
  Re(r) -> Eql(Norm(r),r)
proof 
 ind* Re; r @ 0; 0; x; r1,r2; r1,r2; r
  use Norm_def; Ze
   use Eql_pe_ident_lt; Ze proved..
  use Norm_def; Oe
   use Eql_pe_ident_rt; Oe proved..
  use Norm_def; Ce(x)
   use Eql_pe_ident_lt; Ce(x) proved..
  use Type_of_norm; r1
   use Type_of_norm; r2
    use Type_of_norm; Pe(r1,r2)
     use Eql_trans; Norm Pe(r1,r2); Pe(Norm(r1),Norm(r2)); Pe(r1,r2)
      split Eql(Norm Pe(r1,r2),Pe(Norm(r1),Norm(r2))) & 
            Eql(Pe(Norm(r1),Norm(r2)),Pe(r1,r2)) -> 
            Eql(Norm Pe(r1,r2),Pe(r1,r2)).2,(4,1,1,0),0
       weak* Eql(Norm Pe(r1,r2),Pe(r1,r2))
        use Eql_norm_pe; r1; r2 proved..
       weak* Eql(Norm Pe(r1,r2),Pe(r1,r2))
        use Eql_pe_cong; Norm(r1); Norm(r2); r1; r2 proved..
       proved.....
  use Type_of_norm; r1
   use Type_of_norm; r2
    use Type_of_norm; Te(r1,r2)
     use Eql_trans; Norm Te(r1,r2); Te(Norm(r1),Norm(r2)); Te(r1,r2)
      split Eql(Norm Te(r1,r2),Te(Norm(r1),Norm(r2))) & 
            Eql(Te(Norm(r1),Norm(r2)),Te(r1,r2)) -> 
            Eql(Norm Te(r1,r2),Te(r1,r2)).2,(4,1,1,0),0
       weak* Eql(Norm Te(r1,r2),Te(r1,r2))
        use Eql_norm_te; r1; r2 proved..
       weak* Eql(Norm Te(r1,r2),Te(r1,r2))
        use Eql_te_cong; Norm(r1); Norm(r2); r1; r2 proved..
       proved.....
  use Type_of_norm; r
   use Type_of_norm; Se(r)
    use Eql_trans; Norm Se(r); Se Norm(r); Se(r)
     split Eql(Norm Se(r),Se Norm(r)) & Eql(Se Norm(r),Se(r)) -> 
           Eql(Norm Se(r),Se(r)).2,(4,1,1,0),0
      weak* Eql(Norm Se(r),Se(r))
       use Eql_norm_se; r proved..
      weak* Eql(Norm Se(r),Se(r))
       use Eql_se_cong; Norm(r); r proved..
      proved......

rem 
  \para \bf  Normalizácia spĺňa definíciu  \end 

thm Nre_norm
  Re(r) -> Nre Norm(r)
proof 
 use Norm_def; r
  use Nre_dt; r
   use Nre_de; r
    use Nre_pe.2,1,0; Dt(r); De(r) proved.....

