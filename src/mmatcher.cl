mod Mmatcher logic: 'cl'

incl Mtex

incl Maux

incl Msyntax

incl Mdebug

incl Msemantics

incl Mnorm

rem 
  \para \bf  Verifikácia Harperovho algoritmu  \end 

rem 
  \para \bf  Naivný algoritmus  \end 
  \para \header* fun/2 Ma 'Tex_p2_ma' \end Predpokladajme, že máme zoznam 
  regulárnych výrazov \ft rs \end a slovo \ft w \end, potom predikát 
  \ft Ma(rs,w) \end definujeme nasledovne: 

pred/2 Ma 'Tex_p2_ma'
  Ma(0,0)
  Ma((Oe,rs),w) <- Ma(rs,w)
  Ma((Ce(x),rs),y,w1) <- x = y & Ma(rs,w1)
  Ma((Pe(r1,r2),rs),w) <- Ma((r1,rs),w)
  Ma((Pe(r1,r2),rs),w) <- ~Ma((r1,rs),w) & Ma((r2,rs),w)
  Ma((Te(r1,r2),rs),w) <- Ma((r1,r2,rs),w)
  Ma((Se(r),rs),w) <- Ma(rs,w)
  Ma((Se(r),rs),w) <- ~Ma(rs,w) & Ma((r,Se(r),rs),w)

rem 
  \para \bf  Terminačný predikát  \end 
  \para \header* fun/2 Ma 'Tex_p2_ma' \end Predpokladajme, že máme zoznam 
  regulárnych výrazov \ft rs \end a slovo \ft w \end, potom simulácia 
  terminačného predikátu pre naivný algoritmus z paradigmy totálneho 
  deklaratívneho programovania vyzerá nasledovne: 

pred/2 Tm 
  Tm(0,0)
  Tm(0,w) <- w != 0
  Tm((Ze,rs),w)
  Tm((Oe,rs),w) <- Tm(rs,w)
  Tm((Ce(x),rs),0)
  Tm((Ce(x),rs),y,w1) <- x = y & Tm(rs,w1)
  Tm((Ce(x),rs),y,w1) <- x != y
  Tm((Pe(r1,r2),rs),w) <- Tm((r1,rs),w) & Ma((r1,rs),w)
  Tm((Pe(r1,r2),rs),w) <- Tm((r1,rs),w) & ~Ma((r1,rs),w) & Tm((r2,rs),w)
  Tm((Te(r1,r2),rs),w) <- Tm((r1,r2,rs),w)
  Tm((Se(r),rs),w) <- Tm(rs,w) & Ma(rs,w)
  Tm((Se(r),rs),w) <- Tm(rs,w) & ~Ma(rs,w) & Tm((r,Se(r),rs),w)

rem 
  \para \bf  Miera  \end 
  \para \header* fun/2 Ma 'Tex_p2_ma' \end Predpokladajme, že máme zoznam 
  regulárnych výrazov \ft rs \end a slovo \ft w \end také, že 
  \ft Tm(rs,w) \end. Potom miera z paradigmy totálneho deklaratívneho 
  programovania pre naivný algoritmus vyzerá nasledovne: 

fun/2 M1 'Tex_f2_m1'
  M1(0,w) = 0
  M1((Ze,rs),w) = 0
  M1((Oe,rs),w) = M1(rs,w)+1
  M1((Ce(x),rs),y,w1) = M1(rs,w1)+1 <- x = y
  M1((Ce(x),rs),y,w1) = 0 <- x != y
  M1((Pe(r1,r2),rs),w) = M1((r1,rs),w)+1 <- Ma((r1,rs),w)
  M1((Pe(r1,r2),rs),w) = Max(M1((r1,rs),w),M1((r2,rs),w))+1 <- ~Ma((r1,rs),w)
  M1((Te(r1,r2),rs),w) = M1((r1,r2,rs),w)+1
  M1((Se(r),rs),w) = M1(rs,w)+1 <- Ma(rs,w)
  M1((Se(r),rs),w) = Max(M1(rs,w),M1((r,Se(r),rs),w))+1 <- ~Ma(rs,w)

rem 
  \para \bf  Parciálna korektnosť naivného algortimu  \end 

lemma Tm_pe_rest
  Re(r1) & Re(r2) & Lre(rs) -> Tm((Pe(r1,r2),rs),w) -> Tm((r1,rs),w)
proof 
 cut Ma((r1,rs),w)
  cut Tm((r1,rs),w)
   proved
   proved.
  cut Tm((r1,rs),w)
   proved
   proved...

lemma Tm_se_rest
  Re(r) & Lre(rs) & Tm((Se(r),rs),w) -> Tm(rs,w)
proof 
 cut Tm(rs,w)
  proved
  proved..

rem 
  \para parciálna korektnosť \ft Ma(rs,w) \end cez mieru 

thm Ma_inl
  Lre(rs) & Tm(rs,w) -> Ma(rs,w) <-> Inl(w,Con(rs))
proof 
 indm M1(rs,w) @ rs1,w1
  case Lre; rs @ 0; r1,rs1
   use Inl_oe.0; w proved.
   use Type_of_con; rs1
    case Re; r1 @ 0; 0; x; r2,r3; r2,r3; r
     use Con_ze.0; rs1; w
      use Inl_ze.0; w proved..
     inst \a rs2\a w1(M1(rs2,w1) <= M1(rs1,w) -> Lre(rs2) & Tm(rs2,w1) -> 
                      Ma(rs2,w1) <-> Inl(w1,Con(rs2))).0; rs1; w
      use Con_oe.0; rs1; w proved..
     use Con_ce.0; rs1; w; x
      case Ln; w @ 0; v,w2
       proved
       cut x = v
        inst \a rs2\a w1(M1(rs2,w1) <= M1(rs1,w2) -> Lre(rs2) & Tm(rs2,w1) -> 
                         Ma(rs2,w1) <-> Inl(w1,Con(rs2))).0; rs1; w2
         split* Inl(w2,Con(rs1)) <-> \e w1(w2 = w1 & Inl(w1,Con(rs1))).2,0,0
          inst* \e w1(w2 = w1 & Inl(w1,Con(rs1))); w2 proved.
          eigen \e w1(w2 = w1 & Inl(w1,Con(rs1))).0; w1 proved...
        proved...
     use Tm_pe_rest; r2; r3; rs1; w
      use Con_pe.0; r2; r3; rs1; w
       cut Ma((r2,rs1),w)
        inst \a rs2\a w1(M1(rs2,w1) <= M1((r2,rs1),w) -> 
                         Lre(rs2) & Tm(rs2,w1) -> Ma(rs2,w1) <-> 
                         Inl(w1,Con(rs2))).0; r2,rs1; w proved.
        inst \a rs2\a w1(M1(rs2,w1) <= Max(M1((r2,rs1),w),M1((r3,rs1),w)) -> 
                         Lre(rs2) & Tm(rs2,w1) -> Ma(rs2,w1) <-> 
                         Inl(w1,Con(rs2))).0; r2,rs1; w
         inst \a rs2\a w1(M1(rs2,w1) <= Max(M1((r2,rs1),w),M1((r3,rs1),w)) -> 
                          Lre(rs2) & Tm(rs2,w1) -> Ma(rs2,w1) <-> 
                          Inl(w1,Con(rs2))).0; r3,rs1; w
          use Max_ge.4,0,0; M1((r2,rs1),w); M1((r3,rs1),w)
           use Max_ge.4,1,0; M1((r2,rs1),w); M1((r3,rs1),w) proved.......
     inst \a rs2\a w1(M1(rs2,w1) <= M1((r2,r3,rs1),w) -> 
                      Lre(rs2) & Tm(rs2,w1) -> Ma(rs2,w1) <-> Inl(w1,Con(rs2))).0; r2,r3,rs1; w
      use Con_te.0; r2; r3; rs1; w proved..
     use Tm_se_rest; r; rs1; w
      use Con_se.0; r; rs1; w
       cut Ma(rs1,w)
        inst \a rs2\a w1(M1(rs2,w1) <= M1(rs1,w) -> Lre(rs2) & Tm(rs2,w1) -> 
                         Ma(rs2,w1) <-> Inl(w1,Con(rs2))).0; rs1; w proved.
        inst \a rs2\a w1(M1(rs2,w1) <= Max(M1(rs1,w),M1((r,Se(r),rs1),w)) -> 
                         Lre(rs2) & Tm(rs2,w1) -> Ma(rs2,w1) <-> 
                         Inl(w1,Con(rs2))).0; rs1; w
         inst \a rs2\a w1(M1(rs2,w1) <= Max(M1(rs1,w),M1((r,Se(r),rs1),w)) -> 
                          Lre(rs2) & Tm(rs2,w1) -> Ma(rs2,w1) <-> 
                          Inl(w1,Con(rs2))).0; r,Se(r),rs1; w
          use Max_ge.4,0,0; M1(rs1,w); M1((r,Se(r),rs1),w)
           use Max_ge.4,1,0; M1(rs1,w); M1((r,Se(r),rs1),w) proved............

rem 
  \para \bf  Terminácia naivného algoritmu pre normalizované regulárne 
  výrazy  \end 

lemma Lnre_tm_step
  Nre(r) & \a w1(L(w1) < L(w) -> \a rs(Lnre(rs) -> Tm(rs,w1))) -> 
  \a rs(Lnre(rs) -> ~Inl(0,r) \/ Tm(rs,w) -> Tm((r,rs),w))
proof 
 use Nre_def.2,0,1,0,4,0,0; r
  ind* Re; r @ 0; 0; x; r1,r2; r1,r2; r
   proved
   eigen* \a rs(Lnre(rs) -> ~Inl(0,Oe) \/ Tm(rs,w) -> Tm(rs,w)).0; rs
    use Inl_oe.2,1,0; 0 proved..
   eigen* \a rs(Lnre(rs) -> ~Inl(0,Ce(x)) \/ Tm(rs,w) -> Tm((Ce(x),rs),w)).0; rs
    case Ln; w @ 0; v,w2
     proved
     inst \a w1(L(w1) <= L(w2) -> \a rs(Lnre(rs) -> Tm(rs,w1))):0,2,1,0; w2; rs
      cut x = v
       proved
       proved....
   eigen* \a rs(Lnre(rs) -> ~Inl(0,Pe(r1,r2)) \/ Tm(rs,w) -> 
                Tm((Pe(r1,r2),rs),w)).0; rs
    use Inl_not_pe.0; r1; r2; 0
     cut* ~Inl(0,r1) & ~Inl(0,r2) \/ Tm(rs,w) <-> 
          (~Inl(0,r1) \/ Tm(rs,w)) & (~Inl(0,r2) \/ Tm(rs,w))
      weak* Tm((Pe(r1,r2),rs),w)
       split* (~Inl(0,r1) \/ Tm(rs,w)) & (~Inl(0,r2) \/ Tm(rs,w)).4,0,0,0
        split ~Inl(0,r1) & ~Inl(0,r2) \/ Tm(rs,w).4,0,0,0
         proved
         proved.
        split ~Inl(0,r1) & ~Inl(0,r2) \/ Tm(rs,w).4,0,0,0
         proved
         proved...
      use Nre_pe.2,0,0; r1; r2
       inst \a rs(Lnre(rs) -> ~Inl(0,r1) \/ Tm(rs,w) -> Tm((r1,rs),w)).0; rs
        inst \a rs(Lnre(rs) -> ~Inl(0,r2) \/ Tm(rs,w) -> Tm((r2,rs),w)).0; rs
         cut Ma((r1,rs),w)
          proved
          proved.......
   eigen* \a rs(Lnre(rs) -> ~Inl(0,Te(r1,r2)) \/ Tm(rs,w) -> Tm((r1,r2,rs),w)).0; rs
    use Nre_te.2,0,0; r1; r2
     use Inl_not_te.0; r1; r2
      cut* ~Inl(0,r1) \/ ~Inl(0,r2) \/ Tm(rs,w) -> ~Inl(0,r1) \/ Tm((r2,rs),w)
       weak* Tm((r1,r2,rs),w)
        inst \a rs(Lnre(rs) -> ~Inl(0,r2) \/ Tm(rs,w) -> Tm((r2,rs),w)).0; rs
         split ~Inl(0,r1) \/ ~Inl(0,r2) \/ Tm(rs,w).4,0,0,0,0
          proved
          proved
          proved...
       inst \a rs(Lnre(rs) -> ~Inl(0,r1) \/ Tm(rs,w) -> Tm((r1,rs),w)).0; r2,rs proved.....
   eigen* \a rs(Lnre(rs) -> ~Inl(0,Se(r)) \/ Tm(rs,w) -> Tm((Se(r),rs),w)).0; rs
    use Nre_se.2,0,0; r
     use Inl_se_ie.1,0,2,1,0:0,2,1,2,0,1; r; 0; 0
      use Inl_oe.2,1,0; 0
       inst \a rs(Lnre(rs) -> Tm((r,rs),w)); Se(r),rs
        cut Ma(rs,w)
         proved
         proved.........

rem 
  \para Dvojitá indukcia podľa dĺžky slova a štruktúry zoznamu 

lemma Lnre_tm_struct
  Lnre(rs) & \a w1(L(w1) < L(w) -> \a rs(Lnre(rs) -> Tm(rs,w1))) -> Tm(rs,w)
proof 
 use Type_of_lnre; rs
  ind* Lre; rs @ 0; r,rs
   cut w = 0
    proved
    proved.
   use Lnre_tm_step.0:0,2,1,0; r; w; rs proved....

thm Lnre_tm
  Lnre(rs) -> Tm(rs,w)
proof 
 indm L(w); rs @ w1
  use Lnre_tm_struct.0; rs; w proved...

rem 
  \para \bf  Harperov algoritmus  \end 
  \para Harperov algoritmus pre rozpoznávanie regulárnych výrazov vytvoríme 
  spojením naivného algoritmu a normalizácie pre regulárny výraz \ft r \end 
  a slovo \ft w \end: 
  \eq* 
    Ma((Norm(r),0),w)
  \end

rem 
  \para \bf  Totálna korektnosť Harperovho algoritmu  \end 

thm Harper_cor
  Re(r) -> Ma((Norm(r),0),w) <-> Inl(w,r)
proof 
 use Nre_norm; r
  use Lnre_tm; Norm(r),0; w
   use Nre_def.2,0,1,0,4,0,0; Norm(r)
    use Ma_inl.0; Norm(r),0; w
     use Con_one.0; Norm(r); w
      use Norm_ok; r
       use Eql_def.1,0,2,0,0:0,2,1,2,1,0; Norm(r); r; w proved........

