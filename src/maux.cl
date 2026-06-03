mod Maux logic: 'cl'

incl Mtex

pred/0 Guard 
  Guard <-> \t

fun/2 Max 'Tex_f2_n_max'
  Max(x,y) = x <- x >= y
  Max(x,y) = y <- x < y

thm Max_ge
  Max(x,y) >= x & Max(x,y) >= y
proof 
 case Dich; y,x @ x1,y1; x1,y1
  proved
  proved..

thm Max_lt
  Max(x,y) < z <-> x < z & y < z
proof 
 case Dich; y,x @ x1,y1; x1,y1
  split* x >= z <-> ~(x < z & y < z).2,0,1,(4,0,0,0),0
   proved
   proved
   proved.
  split* y >= z <-> ~(x < z & y < z).2,0,1,(4,0,0,0),0
   proved
   proved
   proved...

fun/2 Min 'Tex_f2_n_min'
  Min(x,y) = y <- x >= y
  Min(x,y) = x <- x < y

thm Min_le
  Min(x,y) <= x & Min(x,y) <= y
proof 
 case Dich; y,x @ x1,y1; x1,y1
  proved
  proved..

thm Min_gt
  Min(x,y) > z <-> x > z & y > z
proof 
 case Dich; y,x @ x1,y1; x1,y1
  split* y <= z <-> ~(x > z & y > z).2,0,1,(4,0,0,0),0
   proved
   proved
   proved.
  split* x <= z <-> ~(x > z & y > z).2,0,1,(4,0,0,0),0
   proved
   proved
   proved...

fun Union 'Tex_f1_ln_union'
  Union(0) = 0
  Union(xs,xss) = xs++Union(xss)

fun L 'Tex_f1_length'
  L(0) = 0
  L(x,xs) = L(xs)+1

