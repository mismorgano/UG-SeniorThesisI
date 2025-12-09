// functions
#let ip(x, y) = $chevron.l #x, #y chevron.r$

// variables
#let l = $cal(l)$
#let epsa = $epsilon.alt$
#let dt = $d t$
#let sign = "sign"
#let L = $L_2[0, 1]$
#let du(X) = $#X'$
#let iso = $tilde.equiv$
#let M = $op(cal(M), limits: #true)$
#let tensor = $times.o$
// #let tensor_p = $attach(tensor, br: pi)$
#let seci(b, x) = math.attach(b, bl: x)
#let secd(b, x) = $attach(#b, br: #x)$
#let Bil(X, Y, Z) = $B(#X, #Y semi #Z)$
#let ct = sym.circle.tiny
#let span = "span"

/// Grothendieck theorem
#let triple(x) = $bar.v.triple #x bar.v.triple$

#let xl = $X^(L)$
#let xu = $X^(U)$
#let yl = $Y^(L)$
#let yu = $Y^(U)$
#let xi = $X_i$
#let yj = $Y_j$

#let apply_definitions(doc) = {
  // macros
  show "tq": [tal que]
  show "tsq": [tales que]
  show "Vs": [espacio vectorial]
  show "Vss": [espacios vectoriales]
  show "Ns": [espacio normado]
  show "Nss": [espacio normados]
  show "Hs": [espacio de Hilbert]
  show "Hss": [espacios de Hilbert]
  show "Bs": [espacio de Banach]
  show "Bss": [espacios de Banach]
  show "Rv": [variable aleatoria]
  show "Rvs": [variables aleatorias]
  show "tp": [producto tensorial]
  show "sucesion": [sucesión]
  doc
}
