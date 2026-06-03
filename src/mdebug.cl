mod Mdebug logic: 'cl'

incl Mtex

incl Maux

incl Msyntax

pred Rec 
  Rec(Ze)
  Rec(Oe)
  Rec Ce(x) <- Ch(x)
  Rec Pe(e1,e2) <- Rec(e1) & Rec(e2)
  Rec Te(e1,e2) <- Rec(e1) & Rec(e2)
  Rec Se(e) <- Rec(e)

pred Lrec 
  Lrec(0)
  Lrec(e,es) <- Rec(e) & Lrec(es)

pred Lch 
  Lch(0)
  Lch(x,xs) <- Ch(x) & Lch(xs)

pred Lstr 
  Lstr(0)
  Lstr(v,w) <- Str(v) & Lstr(w)

fun/3 Insert_acc 
  Insert_acc(x,0,acc) = acc
  Insert_acc(x,(ys,yss),acc) = Insert_acc(x,yss,(x,ys),acc)

fun/2 Insert 
  Insert(x,yss) = Insert_acc(x,yss,0)

fun/3 Perm1_acc 
  Perm1_acc(a,0,acc) = (a,0),acc
  Perm1_acc(a,(b,bs),acc) = (a,b,bs),acc <- a = b
  Perm1_acc(a,(b,bs),acc) = Insert_acc(b,Perm1_acc(a,bs,0),(a,b,bs),acc) <- 
    a != b

fun/2 Perm1 
  Perm1(a,0) = (a,0),0
  Perm1(a,b,bs) = (a,b,bs),0 <- a = b
  Perm1(a,b,bs) = (a,b,bs),Insert(b,Perm1(a,bs)) <- a != b

fun/3 Perms1_acc 
  Perms1_acc(a,0,acc) = acc
  Perms1_acc(a,(bs,bss),acc) = Perms1_acc(a,bss,Perm1_acc(a,bs,acc))

fun/2 Perms1 
  Perms1(a,bss) = Perms1_acc(a,bss,0)

fun/2 Perm_acc 
  Perm_acc(0,acc) = 0,acc
  Perm_acc((a,as),acc) = Perms1_acc(a,Perm_acc(as,0),acc)

fun Perm 
  Perm(a1,0) = (a1,0),0
  Perm(a1,a2,as) = Perms1(a1,Perm(a2,as))

fun/2 Perm_l_acc 
  Perm_l_acc(0,acc) = 0,acc
  Perm_l_acc(((x,0),xys),acc) = Perm_l_acc(xys,acc)
  Perm_l_acc(((x,n+1),xys),acc) = Perms1_acc(x,Perm_l_acc(((x,n),xys),0),acc)

fun Perm_l 
  Perm_l(0) = 0,0
  Perm_l((x,0),xys) = Perm_l(xys)
  Perm_l((x,n+1),xys) = Perms1(x,Perm_l((x,n),xys))

fun/3 Choose_acc 
  Choose_acc(0,xys,acc) = 0,acc
  Choose_acc(n+1,0,acc) = acc
  Choose_acc(n+1,((x,0),xys),acc) = Choose_acc(n+1,xys,acc)
  Choose_acc(n+1,((x,y+1),xys),acc) = 
  Choose_acc(n+1,((x,y),xys),Insert_acc((x,y+1),Choose_acc(n-y,xys,0),acc)) <- 
    n >= y
  Choose_acc(n+1,((x,y+1),xys),acc) = Choose_acc(n+1,((x,n+1),xys),acc) <- n < y

fun/2 Choose 
  Choose(0,xys) = 0,0
  Choose(n+1,0) = 0
  Choose(n+1,(x,0),xys) = Choose(n+1,xys)
  Choose(n+1,(x,y+1),xys) = 
  Insert((x,y+1),Choose(n-y,xys))++Choose(n+1,(x,y),xys) <- 
    n >= y
  Choose(n+1,(x,y+1),xys) = Choose(n+1,(x,n+1),xys) <- n < y

fun/2 Perms_l 
  Perms_l(0,acc) = acc
  Perms_l((xys,xyss),acc) = Perms_l(xyss,Perm_l_acc(xys,acc))

fun/3 Arr_l_acc 
  Arr_l_acc(n,xys,acc) = Perms_l(Choose_acc(n,xys,0),acc)

fun/2 Arr_l 
  Arr_l(n,xys) = Arr_l_acc(n,xys,0)

fun/3 Arrs_l_acc 
  Arrs_l_acc(0,xys,acc) = acc
  Arrs_l_acc(n+1,xys,acc) = Arrs_l_acc(n,xys,Arr_l_acc(n+1,xys,acc))

fun/2 Arrs_l 
  Arrs_l(n,xys) = Arrs_l_acc(n,xys,0)

fun/2 Put_l 
  Put_l(a,0) = (a,1),0
  Put_l(a,(x,n),xys) = (x,n+1),xys <- a = x
  Put_l(a,(x,n),xys) = (x,n),Put_l(a,xys) <- a != x

fun/2 To_l 
  To_l(0,acc) = acc
  To_l((x,xs),acc) = To_l(xs,Put_l(x,acc))

fun/2 Arr 
  Arr(n,xs) = Arr_l(n,To_l(xs,0))

fun/2 Arrs 
  Arrs(n,xs) = Arrs_l(n,To_l(xs,0))

fun/3 Words_acc 
  Words_acc(0,xs,acc) = 0,acc
  Words_acc(n+1,0,acc) = acc
  Words_acc(n+1,(x,xs),acc) = 
  Words_acc(n+1,xs,Perms1_acc(x,Words_acc(n,(x,xs),0),acc))

fun/2 Words 
  Words(n,xs) = Words_acc(n,xs,0)

fun/3 All_words_acc 
  All_words_acc(0,xs,acc) = 0,acc
  All_words_acc(n+1,xs,acc) = All_words_acc(n,xs,Words_acc(n+1,xs,acc))

fun/2 All_words 
  All_words(n,xs) = All_words_acc(n,xs,0)

loc pred Nodoubles 
  Nodoubles(0)
  Nodoubles(x,xs) <- x !in xs & Nodoubles(xs)

rem 
  Perm1("a",'ac') = a:Ls & Perm('aac') = x:Ls & Perm1("a",'bc') = b:Ls & Perm('abc') = y:Ls
  Perm('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab') = x:Ls & Nodoubles(x)
  Perm('aacaaaxaaaab') = x:Ls & Nodoubles(x)
  Arr (2,'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaab') = x :Ls & Nodoubles(x)
  Arr(10,'aaaaaaaaaaaaacaaaaaaaxaaaaaaaaaaaaab') = x:Ls & Nodoubles(x)
  Arr(15,'aaaaaaaaaaaaaaaaaabaaaaaaaaaaab') = x:Ls & Nodoubles(x)
  Arrs (3,'aacaaaxaaaab') = x :Ls & Nodoubles (x)
  Arrs(8,'aacaaaxaaaab') = x:Ls & Nodoubles(x)
  Arrs(3,'abc') = x:Ls & Nodoubles(x)
  Words(2,'abc') = x:Ls & Nodoubles(x)
  All_words(3,'abc') = x:Ls & Nodoubles(x)



