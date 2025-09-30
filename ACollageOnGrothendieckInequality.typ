#import "@preview/ctheorems:1.1.3": thmbox, thmproof, thmrules


// config
#set page(paper: "a4")
#set text(lang: "es", font: "New Computer Modern", size: 12pt)
#set heading(numbering: "1)")

#set cite(form: "prose", style: "alphanumeric")
#show cite: set text(blue)
#show heading.where(level: 1): it => {
  set text(size: 16pt)
  pagebreak(weak: true)
  it
}

#show: thmrules
// envs
#let definition = thmbox("definition", "Definición", inset: 0em)
#let theorem = thmbox("theorem", "Teorema", inset: 0em)
#let proof = thmproof("proof", "Demostración", inset: 0em)

// functions
#let ip(x, y) = $angle.l #x, #y angle.r$

// variables
#let l = $cal(l)$
#let epsa = $epsilon.alt$
#let dt = $d t$
#let sign = "sign"
#let L = $L_2[0, 1]$

// macros
#show "tq": [tal que]
#show "tsq": [tales que]
#show "Hs": [espacio de Hilbert]
#show "Hss": [espacios de Hilbert]
#show "Bs": [espacio de Banach]
#show "rv": [variable aleatoria]
#show "rvs": [variables aleatorias]


#show "sucesion": [sucesión]
// layout

#align(center)[
  #text(size: 18pt)[
    Un Collage de la desigualdad de Grothendieck
  ]
]

= La Desigualdad de Khintchine

Primero veamos un resultado muy importante que nos permitirá después llegar a nuestro objetivo principal,
@Grothendieck_inequality. El siguiente resultado se base en las propiedades de la siguiente clase de funciones: las
*funciones de Rademacher*. Para cada $n in NN$ definimos $r_n:[0, 1]->RR$ definidas por
$
  r_n(t) = sign(sin(2^n pi t)),
$
y la que es su propiedad mas importante, en lo que a nosotros respecta, que la sucesion ${r_n}_n$ forma un conjunto
ortonormal en en #L, y más aún
$
  integral_0^1 abs(sum_n a_n r_n (t))^2 dt = sum_n abs(a_n)^2,
$
para toda ${a_n} in #l _2$


Version de @Tomczak-Jaegermann1989
#theorem[Desigualdad de Khintchine][
  Sea $1 <= p < infinity$. Entonces existen constantes positivas $A_p$ y $B_p$ tsq para toda sucesión de escalares
  ${a_i}$ uno tiene que
  $
    A_p (sum_i abs(a_i)^2)^(1/2) <= (integral_0^1 abs(sum_i r_i (t) a_i)^p d t)^(1/p) <= B_p (sum_i abs(a_i)^2)^(1/2).
  $
  Más aún, $B_p <= p^(1/2)$
]

La siguiente version la podemos encontrar en @jarchow1995absolutely #theorem[Desigualdad de Khintchine][
  Para todo $0 < p < infinity$ existen constantes positivas $A_p$ y $B_p$ tsq para toda sucesión de escalares
  ${a_n} in l_2$ se cumple que
  $
    A_p (sum_n abs(a_n)^2)^(1/2) <= (integral_0^1 abs(sum_n r_n (t) a_n)^p dt)^(1/p) <= B_p (sum_n abs(a_n)^2)^(1/2).
  $
]<Khintchine_inequality>

#proof[
  Mostraremos el resultado para sumas parciales, luego el resultado general se obtiene de un proceso limite, entonces
  tomemos $m in NN$ fijo. Mostraremos primero el resultado para $p$ enteros. Sea $p in NN, y in RR$ y
  ${a_n}_n in #l _2$, notemos que $abs(y)^p < p! (1 + abs(y)^p slash p!) <= p! e^abs(y)$. Por lo cual, definiendo
  $f(t) = sum_(n <= m) a_n r_(n)(t)$, se cumple que
  $
    norm(f)_p^p = integral_0^1 abs(f(t))^p dt <= p! integral_0^1 e^abs(f(t)) dt <= p! integral_0^1 (e^f(t) + e^(-f(t)) ) dt.
  $
  Podemos normalizar $f$ de tal forma que $norm(f)_2 = (sum_(n<=m) a_n^2)^(1/2) = 1$, luego, notemos que
  $
    integral_0^1 e^(f(t)) dt = integral_0^1 exp(sum_(n <= m) a_n r_(n)(t)) dt = integral_0^1 product_(n<=m) exp(a_n r_(n)(t)) dt,
  $
  como las $r_n$ son rvs independientes se cumple que
  $
    integral_0^1 e^(f(t)) dt &= product_(n<=m) integral_0^1 exp(a_n r_(n)(t)) dt = product_(n<=m) integral_0^1 1/2 e^(a_n) + 1/2 e^(-a_n) dt \
    &= product_(n<=m) cosh(a_n),
  $
  comparando con su serie de potencia obtenemos que
  $
    product_(n<=m) cosh(a_n) <= product_(n<=m) exp(a_n^2 / 2) = exp(sum_(n<=m) a_n^2/2) = exp(1/2 sum_(n<=m) a_n^2) = e^(1slash 2).
  $
  Por simetría, también tenemos que $integral_0^1 e^(-f(t)) dt <= e^(1 slash 2)$, y por tanto
  $
    norm(f)_p^p <= 2p! e^(1 slash 2).
  $
  Para $2<= p < infinity$, por la monotonía de las normas $L_p$ se puede concluir, para $a_1, dots, a_m in RR$
  arbitrarios, que
  $
    (sum_(n<=m) a_n^2)^(1/2) = norm(sum_(n<=m) a_n r_n)_2 <= norm(sum_(n<=m) a_n r_n)_p,
  $
  luego por la homogeneidad de las normas, tenemos que
  $
    1/((sum_(n<=m) a_n^2)^(1/2)) norm(sum_(n<=m) a_n r_n)_p <= 1/((sum_(n<=m) a_n^2)^(1/2)) norm(sum_(n<=m) a_n r_n)_(ceil(p)) <= (2ceil(p)! e^(1 slash 2))^(1/ceil(p)),
  $
  por lo cual concluimos que
  $
    (sum_(n<=m) a_n^2)^(1/2) <= norm(sum_(n<=m) a_n r_n)_p <= (2ceil(p)! e^(1 slash 2))^(1/ceil(p)) (sum_(n<=m) a_n^2)^(1/2),
  $
  como queremos.

  Ahora, para el caso $0 < p < 2$. Sea $theta = (2-(p/2))^(-1)$, podemos notar que $0 < theta < 1$, asi $1/theta > 1$ y
  su conjugado es $1/(1-theta)$, ademas $p theta + 4(1-theta) = 2$, por lo cual aplicando la desigualdad de Hölder se
  cumple que
  $
    integral_0^1 abs(f(t))^2 dt = integral_0^1 abs(f(t))^(p theta) abs(f(t))^(4 (1 - theta)) dt &<= (integral_0^1 (abs(f(t))^(p theta))^(1/theta) dt)^theta (integral_0^1 abs(f(t))^(4 (1 - theta))^(1/(1-theta)) dt)^(1-theta) \
    &= (integral_0^1 (abs(f(t))^p dt)^theta (integral_0^1 abs(f(t))^4 dt)^(1-theta),
  $
  lo cual se puede reescribir como $norm(f)_2^2 <= norm(f)_p^(p theta) norm(f)_4^(4(1-theta))$. Por lo probado
  anteriormente tenemos que $norm(f)_4 <= B_4 norm(f)_2$, por lo cual
  $
    norm(f)_2^2 <= norm(f)_p^(p theta) norm(f)_4^(4(1-theta)) <= norm(f)_p^(p theta) B_4^(4(1-theta)) norm(f)_2^(4(1-theta)),
  $
  y en consecuencia
  $
    B_4^(-4(1-theta)) norm(f)_2^(2-4(1-theta)) = B_4^(p theta -2 )norm(f)_2^(p theta)<= norm(f)_p^(p theta),
  $
  obteniendo que
  $
    B_4^(1 - 2slash p theta) norm(f)_2 <= norm(f)_p,
  $
  como $1 - 2slash p theta = 2 - 4slash p$, vemos que $B_4^(2 - 4slash p) norm(f)_2 <= norm(f)_p$. Luego, por la
  monotonía obtenemos que $B_4^(2 - 4slash p) norm(f)_2 <= norm(f)_p <= norm(f)_2$.
]<Khintchine_inequality_proof>

Version que se encuentra en @Garling_2007
#theorem[Desigualdad de Khintchine][
  Existen constantes $A_p$ y $B_p$, para $0 < p < infinity$, tq si $a_1, dots, a_N$ son números reales y
  $epsa_1, dots, epsa_N$ son rvs Bernoulli, entonces
  $
    A_p norm(s_N)_p <= sigma <= B_p norm(s_N)_p,
  $
  donde $s_N = sum_(n=1)^N epsa_n a_n$ y $sigma^2 = norm(s_N)_2^2 = sum_(n=1)^N a_n^2$
]


= La Desigualdad de Grothendieck.

Ahora veamos la Demostración del Teorema más importante, nuestro objetivo principal.

Primera version, extraída de @Tomczak-Jaegermann1989
#theorem[
  Sea ${a_(i j)}_(i, j =1)^n$ una matriz escalar y supongamos que
  $
    abs(sum_(i) sum_(i) a_(i j) s_i t_j) <= 1,
  $
  para todas las sucesiones de escalares ${s_i}$ y ${t_i}$ tsq $max abs(s_i) <=1$ y $max abs(t_i) <=1$. Entonces existe
  una constante universal $K_G$ tq
  $
    abs(sum_(i) sum_(j) a_(i j) ip(x_i, y_i)) <= K_G norm({x_i})_infinity norm({y_i})_infinity,
  $
  para todas las sucesiones ${x_i}$ y ${y_i}$ en $cal(l)_2^k$, $k in NN$.
]

Segunda version, encontrada en @jarchow1995absolutely

#theorem[Desigualdad de Grothendieck][
  Existe una constante universal $K_G$ para la cual, dado cualquier Hs $H$, cualquier $n in NN$, y cualquier matriz
  escalar $(a_(i j))$ y cualesquiera vectores en $x_1, dots, x_n, y_1, dots, y_n in B_H$, tenemos que
  $
    abs(sum_(i, j) a_(i j) ip(x_i, y_i)) <= K_G max{ abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1}.
  $
]<Grothendieck_inequality>
#proof[
  #let triple(x) = $bar.v.triple #x bar.v.triple$


  #let xl = $X^(L)$
  #let xu = $X^(U)$
  #let yl = $Y^(L)$
  #let yu = $Y^(U)$
  #let xi = $X_i$
  #let yj = $Y_j$
  Supondremos que las matrices son reales al igual que los Hs. Por simplicidad, definamos:
  $
    norm(a) := sup{ abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1}
  $
  y
  $
    triple(a) := sup abs(sum_(i, j) a_(i j) ip(x_i, y_i)),
  $
  donde este ultimo supremo se toma sobre todos los Hss $H$ y todos los vectores $x_1, dots, x_n$, $y_1, dots, y_n$ en
  la bola unitaria $B_H$ del Hs $H$. Dado que para cada $n$ solo consideremos un conjunto finito de vectores entonces
  solo es necesario considerar Hss separables.

  Al igual que con la @Khintchine_inequality_proof de la desigualdad de Khintchine la idea es es poder embeber cualquier
  Hs separable en $L_2[0, 1]$ que respete su producto interno. Para ello, de igual manera, utilizaremos las funciones de
  Rademacher ${r_n}_n$ las cuales formal un conjunto ortonormal en $L$. La forma en que lo haremos sera la siguiente:
  dado $x in H$, como $H$ tiene base ortonormal ${e_n}_n$ sabemos que $x = sum_n ip(x, e_n) e_n$ y ademas
  $infinity > norm(x) = sum_(n) ip(x, e_n)$, asi podemos definir $X:[0, 1] -> RR$ como
  $
    X(t) := sum_(n) ip(x, e_n)r_n(t).
  $
  Luego, por la ortonormalidad de las funciones de Rademacher tenemos que
  $
    norm(X)_2^2 = integral_0^1 X(t)^2 dt = integral_0^1 abs(sum_(n) ip(x, e_n)r_n(t))^2 dt = integral_0^1 sum_(n) ip(x, e_n)^2 dt = norm(x)^2,
  $
  por lo cual $norm(X)_2 = norm(x)$ y ademas, si $y in H$ al igual que con $x$ podemos definir $Y:[0, 1] -> infinity$ y
  tenemos que
  $
    ip(x, y) & = 1/4 (norm(x+y)^2 - norm(x-y)^2) \
             & = 1/4 (integral_0^1 (X(t) - Y(t))^2 dt - integral_0^1 (X(t) - Y(t))^2 dt ) \
             & = integral_0^1 X(t)Y(t) dt,
  $
  por lo cual se preserva el producto interno. La idea ahora es acotar $X$ de cierta manera. Para ellos, tomemos $M > 0$
  y definamos $X^L:[0, 1]->RR$ dada por
  $
    xl(t) := cases(X(t) & "si" abs(X(t)) <= M, M sign X(t) & "si" abs(X(t))>M)
  $
  y también definamos $xu:[0, 1] -> RR$ dada por $xu := X(t) - xl$. De lo anterior podemos notar que $xl$ esta acotada
  por $M$ y que
  $
    xu(t) = cases(0 &"si" abs(X(t))<=M, X(t) - M sign X(t) & "si" abs(X(t))> M)
  $
  por lo cual
  $
    abs(xu(t)) = cases(0 & "si" abs(X(t))<=M, abs(X(t)) - M & "si" abs(X(t))> M),
  $
  mas aun, usando la siguiente desigualdad $s<= m + (s^2)/4m$, con $s, m > 0$, tenemos que
  $
    abs(X(t)) <= M + (abs(X(t))^2)/(4M) ==> abs(xu(t)) <= abs(X(t))^2/(4M).
  $
  Por lo cual, si suponemos que $x in B_H$ y usando la @Khintchine_inequality obtenemos que
  $
    norm(xu)_2^2 = integral_0^1 abs(xu(t))^2 dt <= 1/(16M^2) integral_0^1 abs(X(t))^4 dt <= B_4^4/(16M^2) norm(x)_2^2 <= 3/(16M^2),
  $
  donde la ultimo desigualdad se da pues $B_4 <= 3^(1/4)$. Lo anterior implica que para $x in B_H$ se cumple que
  $norm(xu)_2 <= sqrt(3)/(4M)$. Por ultimo, primero notemos que $X = xu + xl$, por lo cual
  $X Y = (xu + xl)(yu + yl) = (xu + xl)(yl) + (X)(yu) = xl yl + (xu yl + x yu)$. Luego, si $x_1, dots, x_n$ y
  $y_1, dots, y_n in B_H$, usando lo anterior y la desigualdad del trianguló se cumple que
  $
    abs(sum_(i, j) a_(i j) ip(x_i, y_i)) &= abs(integral_0^1 sum_(i, j) a_(i, j) xi(t) yj(t) dt) \
    &= abs(integral_0^1 sum_(i, j) a_(i, j) (xl_i (t) yl_j (t) + (xu_i (t) yl_j (t) + X(t)yu_j (t))) dt) \
    & <= abs(integral_0^1 sum_(i, j) a_(i, j) xl_i (t) yl_j (t) dt) + abs(integral_0^1 sum_(i, j) a_(i, j) (xu_i (t) yl_j (t) + X(t)yu_j (t)) dt).
  $
  Por un lado tenemos que
  $
    abs(integral_0^1 sum_(i, j) a_(i, j) xl_i (t) yl_j (t) dt) <= M^2 abs(integral_0^1 sum_(i, j) a_(i, j) dt) <= M^2 norm(a),
  $
  por otro lado
  $
    abs(integral_0^1 sum_(i, j) a_(i, j) (xu_i (t) yl_j (t) + X(t)yu_j (t)) dt) = \
    abs(
      integral_0^1 sum_(i, j) a_(i, j) norm(xu_i (t))(xu_i (t) yl_j (t))/(norm(xu_i (t))) + (X(t)yu_j (t))/norm(yl_j (t)) norm(yl_j (t)) dt
    ) \
    <= abs(integral_0^1 sum_(i, j) a_(i, j) norm(xu_i (t))(xu_i (t) yl_j (t))/(norm(xu_i (t))) dt) + abs(integral_0^1 sum_(i, j) a_(i, j) (X(t)yu_j (t))/norm(yl_j (t)) norm(yl_j (t)) dt),
  $
  de donde se puede ver que
  $
    abs(integral_0^1 sum_(i, j) a_(i, j) norm(xu_i (t))(xu_i (t) yl_j (t))/(norm(xu_i (t))) dt) <= sqrt(3)/(4M) abs(integral_0^1 sum_(i, j) a_(i, j) (xu_i (t) yl_j (t))/(norm(xu_i (t))) dt)
  $
  (lo cual debería implicar $<= sqrt(3)/(4M) triple(a)$) y que
  $
    abs(integral_0^1 sum_(i, j) a_(i, j) (X(t)yu_j (t))/norm(yl_j (t)) norm(yl_j (t)) dt) &<= sqrt(3)/(4M) abs(integral_0^1 sum_(i, j) a_(i, j) (X(t)yu_j (t))/norm(yl_j (t)) dt) \
    &<= sqrt(3)/(4M) triple(a).
  $
  De lo anterior obtenemos que
  $
    abs(sum_(i, j) a_(i j) ip(x_i, y_i)) <= M^2 norm(a) + sqrt(3)/(2M) triple(a),
  $
  entonces, si $M>sqrt(3)/2$, lo anterior implica que
  $
    triple(a) <= (2M^3)/(2M - sqrt(3)) norm(a),
  $
  como queremos.
]

Una tercera version, se encuentra en @Lindenstrauss1996

#theorem[
  Sea $(a_(i, j))$ una matriz escalar tq
  $abs(sum_(i) sum_(i) a_(i j) s_i t_j) <= 1,$
  para todas las sucesiones de escalares ${s_i}$ y ${t_i}$ tsq $max abs(s_i) <=1$ y $max abs(t_i) <=1$. Entonces existe
  una constante universal $K_G$ tq
  $
    abs(sum_(i) sum_(j) a_(i j) ip(x_i, y_i)) <= K_G norm({x_i})_infinity norm({y_i})_infinity,
  $
  para toda colección de vectores ${x_i}$ y ${y_i}$ en un Hs.
]

Una cuarta version (más general?) dada en @Garling_2007, para ello consideremos
$
  norm(A) & = sup {sum_(i=1)^m abs(sum_(j=1)^n a_(i j) t_j): abs(t_j) <= 1} \
          & = sup {sum_(i=1)^m abs(sum_(j=1)^n a_(i j) s_i t_j): abs(s_i) <= 1, abs(t_j) <= 1}.
$
Notar que $norm(A)$ es simplemente es la norma del operador $T_A: #l^n_infinity -> #l^m_1$, dado por
$T_A (t) = (sum_(j=1)^n a_(i j) t_j)_(i=1)^m$, para $t = (t_1, dots, t_n) in #l^n_infinity$.

De manera similar. Definamos
$
  g(A) & = sup {sum_(i=1)^m norm(sum_(j=1)^n a_(i j) k_j): k_j in H, norm(k_j) <= 1} \
       & = sup {abs(sum_(i=1)^m sum_(j=1)^n a_(i j) ip(h_i, k_j)): h_i, k_j in H, norm(h_i) <= 1, norm(k_j) <= 1},
$
donde $H$ es un Hs real o complejo. Al igual que antes $g(A)$ es simplemente es la norma del operador
$T_A: #l^n_infinity (H) -> #l^m_1 (H)$, dado por $T_A (k) = (sum_(j=1)^n a_(i j) k_j)_(i=1)^m$, para
$k = (k_1, dots, k_n) in #l^n_infinity (H)$.

#theorem[Desigualdad de Grothendieck][
  Existe una constante $C$, independiente de $m$ y $n$, tq si $A in cal(M)_(m, n)$ entonces $g(A) <= C norm(A)$
]

También tenemos la siguiente version dada en @Wojtaszczyk_1991 que depende de otro resultado:

#theorem[Grothendieck][
  Todo operador $T:L_1(mu) -> H$, donde $H$ es un Hs, es absolutamente-$1$ sumable
]

#theorem[Desigualdad de Grothendieck][
  Sea $(a_(n, m))_(n, m = 1)^N$ una matriz finita o infinita tal que para cualesquiera dos sucesiones de escalares
  $(alpha_n)_(n=1)^N$ y $(beta_m)_(m=1)^N$ tenemos que
  $
    abs(sum_(n, m=1)^N a_(n, m) alpha_n beta_m) <= sup_n abs(alpha_n) sup_n abs(beta_n).
  $
  Entonces para cualesquiera dos sucesiones $(h_n)_(n=1)^N$ y $(k_m)_(m=1)^N$ es un Hs arbitrario $H$ tenemos que:
  $
    abs(sum_(n, m=1)^N a_(n, m) ip(h_n, k_m)) = K_G sup_n norm(h_n) sup_m norm(k_m),
  $
  donde $K_G$ es la constante de Grothendieck.
]


#bibliography("biblio.yml", full: true)
