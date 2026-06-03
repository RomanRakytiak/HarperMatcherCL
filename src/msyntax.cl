mod Msyntax logic: 'cl'

incl Mtex

incl Maux

rem 
  \para \bf  Aritmetizácia syntaxe  \end 

rem 
  \para Knoštruktory regulárnych výrazov: 

fun/0 Ze 'Tex_f0_rebze'
  Ze = 0,0

fun/0 Oe 'Tex_f0_reboe'
  Oe = 1,0

fun Ce 'Tex_f1_re_ce'
  Ce(x) = 2,x

fun/2 Pe 'Tex_f2_re_ue'
  Pe(r1,r2) = 3,r1,r2

fun/2 Te 'Tex_f2_re_ae'
  Te(r1,r2) = 4,r1,r2

fun Se 'Tex_f1_re_se'
  Se(r) = 5,r

rem 
  \para Predikát pre kód korektného regulárneho výrazu. 

pred Re 
  Re(Ze)
  Re(Oe)
  Re Ce(x) <- N(x)
  Re Pe(r1,r2) <- Re(r1) & Re(r2)
  Re Te(r1,r2) <- Re(r1) & Re(r2)
  Re Se(r) <- Re(r)

rem 
  \para Konečná iterácia výrazu. 

fun/2 Ie 'Tex_f2_re_ie'
  Ie(r,0) = Oe
  Ie(r,n+1) = Te(r,Ie(r,n))

thm Type_of_ie
  Re(r) -> Re Ie(r,n)
proof 
 ind N; n @ 0; n
  proved
  proved..

rem 
  \para Predikát pre kód korektného zoznamu regulárnych výrazov. 

pred Lre 
  Lre(0)
  Lre(r,rs) <- Re(r) & Lre(rs)

thm Lre_in
  Lre(xs) -> r in xs -> Re(r)
proof 
 ind Lre; xs @ 0; e,es
  proved
  split r = e \/ r in es.4,0,0,0
   proved
   proved...

thm Lre_con
  Lre(xs) & Lre(ys) -> Lre(xs++ys)
proof 
 ind Lre; xs @ 0; r,es
  proved
  proved..

rem 
  \para Zreťazenie zoznamu výrazov. 

fun Con 'Tex_f1_ln_con'
  Con(0) = Oe
  Con(r,rs) = Te(r,Con(rs))

thm Type_of_con
  Lre(rs) -> Re Con(rs)
proof 
 ind Ln; rs @ 0; v,w
  proved
  proved..

rem 
  \para Podvýraz regulárneho výrazu. 

pred/2 Sub 'Tex_p2_sub'
  Sub(r,Ze) <- Ze = r
  Sub(r,Oe) <- Oe = r
  Sub(r,Ce(y)) <- r = Ce(x) & x = y
  Sub(r,Pe(s1,s2)) <- Pe(s1,s2) = r
  Sub(r,Pe(s1,s2)) <- Pe(s1,s2) != r & Sub(r,s1)
  Sub(r,Pe(s1,s2)) <- Pe(s1,s2) != r & ~Sub(r,s1) & Sub(r,s2)
  Sub(r,Te(s1,s2)) <- Te(s1,s2) = r
  Sub(r,Te(s1,s2)) <- Te(s1,s2) != r & Sub(r,s1)
  Sub(r,Te(s1,s2)) <- Te(s1,s2) != r & ~Sub(r,s1) & Sub(r,s2)
  Sub(r,Se(s1)) <- Se(s1) = r
  Sub(r,Se(s1)) <- Se(s1) != r & Sub(r,s1)

thm Sub_ze
  Re(r) -> Sub(r,Ze) <-> r = Ze
proof  proved.

thm Sub_oe
  Re(r) -> Sub(r,Oe) <-> r = Oe
proof  proved.

thm Sub_ce
  Re(r) -> Sub(r,Ce(x)) <-> r = Ce(x)
proof 
 case Re; r @ 0; 0; x1; r1,r2; r1,r2; r1
  proved
  proved
  proved
  proved
  proved
  proved..

thm Sub_pe
  Re(r) & Re(s1) & Re(s2) -> Sub(r,Pe(s1,s2)) <-> 
  r = Pe(s1,s2) \/ Sub(r,s1) \/ Sub(r,s2)
proof 
 cut Pe(s1,s2) = r
  proved
  cut Sub(r,s1)
   proved
   proved...

thm Sub_te
  Re(r) & Re(s1) & Re(s2) -> Sub(r,Te(s1,s2)) <-> 
  r = Te(s1,s2) \/ Sub(r,s1) \/ Sub(r,s2)
proof 
 cut Te(s1,s2) = r
  proved
  cut Sub(r,s1)
   proved
   proved...

thm Sub_se
  Re(r) & Re(s1) -> Sub(r,Se(s1)) <-> r = Se(s1) \/ Sub(r,s1)
proof 
 cut Se(s1) = r
  proved
  proved..

