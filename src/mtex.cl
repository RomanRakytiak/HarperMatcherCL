mod Mtex

appldisp/0 Tex_f0_foo
  Std('?',0)

appldisp/0 Tex_p0_poo
  Std('?',0)

appldisp/2 Tex_f2_sq_inl_unf
  Frac(Op(Ent('vellip'),0),1,
       Infix(Arg(0),25,1,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(1))))

fun/0 Foo 'Tex_f0_foo'
  Foo = 0

pred/0 Poo 'Tex_p0_poo'
  Poo <-> \f

fun/2 S_foo 'Tex_f2_sq_inl_unf'
  S_foo(xs,r) = 0

appldisp/1 Tex_f1_length
  Prefix(90,2,Id(4,'L',0),Arg(0))

appldisp/0 Tex_f0_re_ze
  Id(0,Ent('emptyset'),0)

appldisp/0 Tex_f0_rebze
  Id(2,'0',0)

appldisp/0 Tex_f0_reboe
  Id(2,'1',0)

appldisp/0 Tex_f0_re_ee
  Id(0,Ent('epsi'),0)

appldisp/0 Tex_f0_re_ee_
  Fenced(Op('{',0),Id(0,Ent('epsi'),0),Op('}',0))

appldisp/1 Tex_f1_re_ce
  Std('ch',0)

appldisp/1 Tex_f1_re_ce_
  Fenced(Op(Ent('lang'),0),Arg(0),Op(Ent('rang'),0))

appldisp/2 Tex_f2_re_ae
  Infix(Arg(0),45,1,Op(Ent('sdot'),0),Arg(1))

appldisp/2 Tex_f2_re_ue
  Infix(Arg(0),40,1,Op('+',0),Arg(1))

appldisp/1 Tex_f1_re_se
  Subsup(Arg(0),75,None,Id(0,'*',0))

appldisp/2 Tex_p2_ma
  Std('Match',0)

appldisp/2 Tex_f2_m1
  Std('m',0)

appldisp/2 Tex_f2_n_max
  Std('max',0)

appldisp/2 Tex_f2_n_min
  Std('min',0)

appldisp/2 Tex_f2_eand
  Infix(Arg(0),45,1,Op(Ent('otimes'),0),Arg(1))

appldisp/2 Tex_f2_eor
  Infix(Arg(0),40,1,Op(Ent('oplus'),0),Arg(1))

appldisp/1 Tex_f1_re_dt_
  Std('d',0)

appldisp/1 Tex_f1_re_dt
  Prefix(90,2,Op(Ent('delta'),0),Arg(0))

appldisp/1 Tex_f1_re_de
  Subsup(Arg(0),75,None,Id(0,'-',0))

appldisp/1 Tex_f1_sq_axiom
  Underover(Arg(0),None,Op(Ent('UnderBar'),0))

appldisp/1 Tex_f1_sq_def
  Postfix(Underover(Arg(0),None,Op(Ent('UnderBar'),0)),60,1,
          Fenced(Op('(',0),Id(6,'def',0),Op(')',0)))

appldisp/1 Tex_f1_sq_rfl
  Postfix(Underover(Arg(0),None,Op(Ent('UnderBar'),0)),60,1,
          Fenced(Op('(',0),Id(6,'rfl',0),Op(')',0)))

appldisp/2 Tex_f2_sq_1
  Frac(Arg(0),1,Arg(1))

appldisp/2 Tex_f2_sq_sym
  Postfix(Frac(Arg(0),1,Arg(1)),60,1,Fenced(Op('(',0),Id(6,'sym',0),Op(')',0)))

appldisp/2 Tex_f2_sq_red
  Postfix(Frac(Arg(0),1,Arg(1)),60,1,Fenced(Op('(',0),Id(6,'red',0),Op(')',0)))

appldisp/3 Tex_f3_sq_2
  Frac(Infix(Arg(0),50,1,Op(Ent('imath'),0),Arg(1)),1,Arg(2))

appldisp/3 Tex_f3_sq_tran
  Postfix(Frac(Infix(Arg(0),50,1,Op(Ent('imath'),0),Arg(1)),1,Arg(2)),60,1,
          Fenced(Op('(',0),Id(6,'tran',0),Op(')',0)))

appldisp/3 Tex_f3_sq_splt
  Postfix(Frac(Infix(Arg(0),50,1,Op(Ent('imath'),0),Arg(1)),1,Arg(2)),60,1,
          Fenced(Op('(',0),Id(6,'splt',0),Op(')',0)))

appldisp/3 Tex_f3_sq_appl
  Postfix(Frac(Infix(Arg(0),50,1,Op(Ent('imath'),0),Arg(1)),1,Arg(2)),60,1,
          Fenced(Op('(',0),Id(6,'appl',0),Op(')',0)))

appldisp/2 Tex_f2_sq_ax
  Infix(Arg(0),20,1,Op(Ent('rArr'),0),Arg(1))

appldisp/2 Tex_f2_eqv
  Infix(Arg(0),20,2,Op(Ent('hArr'),0),Arg(1))

appldisp/2 Tex_f2_match
  Infix(Arg(0),10,2,Id(6,'matches',0),Arg(1))

appldisp/3 Tex_f3_sq_un
  Frac(Arg(0),1,Infix(Arg(1),40,1,Op(Ent('rArr'),0),Arg(2)))

appldisp/4 Tex_f4_sq_bin
  Frac(Infix(Arg(0),40,1,Op(Ent('imath'),0),Arg(1)),1,
       Infix(Arg(2),40,1,Op(Ent('rArr'),0),Arg(3)))

appldisp/2 Tex_f2_sq_inl_ax
  Underover(Infix(Arg(0),40,1,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(1))),
            None,Op(Ent('UnderBar'),0))

appldisp/1 Tex_f1_sq_inl_empty
  Subsup(Underover(Infix(Num('0',0),25,1,Op(Ent('isin'),0),
                         Prefix(90,2,Id(0,'L',0),Arg(0))),None,Op(Ent('UnderBar'),0)),
         30,None,Fenced(Op('(',0),Id(2,'empty',0),Op(')',0)))

appldisp/0 Tex_f0_sq_inl_oe_def
  Subsup(Underover(Infix(Num('0',0),25,1,Op(Ent('isin'),0),
                         Prefix(90,2,Id(0,'L',0),Fenced(Op('(',0),Id(2,'1',0),Op(')',0)))),
                   None,Op(Ent('UnderBar'),0)),30,None,
         Fenced(Op('(',0),Id(2,'def empty',0),Op(')',0)))

appldisp/1 Tex_f1_sq_inl_se_def
  Subsup(Underover(Infix(Num('0',0),25,1,Op(Ent('isin'),0),
                         Prefix(90,2,Id(0,'L',0),
                                Fenced(Op('(',0),Subsup(Arg(0),75,None,Id(0,'*',0)),
                                       Op(')',0)))),None,Op(Ent('UnderBar'),0)),30,
         None,Fenced(Op('(',0),Id(2,'zero iter',0),Op(')',0)))

appldisp/1 Tex_f1_sq_inl_char
  Subsup(Underover(Infix(Fenced(Op('(',0),Infix(Id(1,'c',0),40,1,Op(',',0),Num('0',0)),
                                Op(')',0)),25,1,Op(Ent('isin'),0),
                         Prefix(90,2,Id(0,'L',0),
                                Prefix(70,2,Id(0,'ch',0),
                                       Fenced(Op('(',0),Id(1,'c',0),Op(')',0))))),
                   None,Op(Ent('UnderBar'),0)),30,None,
         Fenced(Op('(',0),
                Infix(Id(2,'def',0),10,1,Id(0,' ',0),
                      Infix(Id(1,'c',0),40,1,Op('=',0),Arg(0))),Op(')',0)))

appldisp/5 Tex_f5_sq_inl_sim
  Frac(Infix(Infix(Arg(0),15,0,Op(Ent('rarr'),0),Arg(1)),10,0,Op(Ent('mid'),0),
             Arg(2)),1,
       Infix(Arg(3),40,1,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(4))))

appldisp/3 Tex_f3_sq_inl_lt
  Postfix(Frac(Arg(0),1,
               Infix(Arg(1),25,0,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(2)))),
          60,1,Fenced(Op('(',0),Id(6,'left',0),Op(')',0)))

appldisp/4 Tex_f4_sq_inl_pe_lt
  Postfix(Frac(Arg(0),1,
               Infix(Arg(1),25,0,Op(Ent('isin'),0),
                     Prefix(90,2,Id(0,'L',0),
                            Fenced(Op('(',0),Infix(Arg(2),40,1,Op('+',0),Arg(3)),
                                   Op(')',0))))),60,1,
          Fenced(Op('(',0),Id(6,'left',0),Op(')',0)))

appldisp/3 Tex_f3_sq_inl_rt
  Postfix(Frac(Arg(0),1,
               Infix(Arg(1),25,0,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(2)))),
          60,1,Fenced(Op('(',0),Id(6,'right',0),Op(')',0)))

appldisp/4 Tex_f4_sq_inl_pe_rt
  Postfix(Frac(Arg(0),1,
               Infix(Arg(1),25,0,Op(Ent('isin'),0),
                     Prefix(90,2,Id(0,'L',0),
                            Fenced(Op('(',0),Infix(Arg(2),40,1,Op('+',0),Arg(3)),
                                   Op(')',0))))),60,1,
          Fenced(Op('(',0),Id(6,'right',0),Op(')',0)))

appldisp/3 Tex_f3_sq_inl_iter
  Postfix(Frac(Arg(0),1,
               Infix(Arg(1),25,0,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(2)))),
          60,1,Fenced(Op('(',0),Id(6,'iter',0),Op(')',0)))

appldisp/5 Tex_f5_sq_inl_se_iter
  Postfix(Frac(Infix(Arg(0),10,1,Op(Ent('mid'),0),Arg(1)),1,
               Infix(Infix(Arg(2),35,1,Op(Ent('oplus'),0),Arg(3)),25,1,
                     Op(Ent('isin'),0),
                     Prefix(90,2,Id(0,'L',0),
                            Fenced(Op('(',0),Subsup(Arg(4),75,None,Id(0,'*',0)),
                                   Op(')',0))))),60,1,
          Fenced(Op('(',0),Id(2,'iter',0),Op(')',0)))

appldisp/4 Tex_f4_sq_inl_split
  Postfix(Frac(Infix(Arg(0),10,0,Op(Ent('mid'),0),Arg(1)),1,
               Infix(Arg(2),25,0,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(3)))),
          60,1,Fenced(Op('(',0),Id(6,'split',0),Op(')',0)))

appldisp/6 Tex_f6_sq_inl_te_split
  Postfix(Frac(Infix(Arg(0),10,1,Op(Ent('mid'),0),Arg(1)),1,
               Infix(Infix(Arg(2),35,1,Op(Ent('oplus'),0),Arg(3)),25,1,
                     Op(Ent('isin'),0),
                     Prefix(90,2,Id(0,'L',0),
                            Fenced(Op('(',0),
                                   Infix(Arg(4),45,1,Op(Ent('sdot'),0),Arg(5)),
                                   Op(')',0))))),60,1,
          Fenced(Op('(',0),Id(2,'split',0),Op(')',0)))

appldisp/3 Tex_p3_proves_inl
  Infix(Arg(0),10,1,Op(Ent('vdash'),0),
        Infix(Arg(1),15,1,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(2))))

appldisp/1 Disp2
  Infix(Arg(0),40,1,Op(Ent('vdash'),0),Id(0,'id',0))

appldisp/1 Disp1
  Postfix(Arg(0),60,1,Fenced(Op('(',0),Id(0,'rfl',0),Op(')',0)))

appldisp/2 Tex_f2_re_ie
  Subsup(Arg(0),79,None,Arg(1))

appldisp/1 Tex_f1_ln_union
  Prefix(70,2,Op(Ent('xcup'),0),Arg(0))

appldisp/1 Tex_f1_ln_con
  Prefix(70,2,Op(Ent('prod'),0),Arg(0))

appldisp/1 Tex_p1_inl_empty
  Infix(Num('0',0),25,1,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(0)))

appldisp/1 Tex_p1_inl_not_null
  Infix(Num('0',0),25,1,Op(Ent('notin'),0),Prefix(90,2,Id(0,'L',0),Arg(0)))

appldisp/2 Tex_p2_inl
  Infix(Arg(0),25,0,Op(Ent('isin'),0),Prefix(90,2,Id(0,'L',0),Arg(1)))

appldisp/2 Tex_p2_eql
  Infix(Prefix(90,2,Id(0,'L',0),Arg(0)),18,0,Op('=',0),Prefix(90,2,Id(0,'L',0),Arg(1)))

appldisp/2 Tex_p2_lel
  Infix(Prefix(90,2,Id(0,'L',0),Arg(0)),18,0,Op(Ent('sube'),0),
        Prefix(90,2,Id(0,'L',0),Arg(1)))

appldisp/2 Tex_p2_sub
  Infix(Arg(0),18,1,Op(Ent('ltrie'),0),Arg(1))

