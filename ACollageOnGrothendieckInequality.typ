#import "@preview/ctheorems:1.1.3": thmbox, thmrules, thmproof


// config
#set page(paper: "a4")
#set text(lang: "es", font: "New Computer Modern", size: 12pt)
#set heading(numbering: "1")

#set cite(form: "prose", style: "alphanumeric")
#show cite: set text(blue)

#show: thmrules
// envs
#let theorem = thmbox("theorem", "Teorema", inset: 0em)
#let proof = thmproof("proof", "Demostración", inset: 0em)

// functions
#let ip(x, y) = $angle.l #x, #y angle.r$
#let l = $cal(l)$
#let epsa = $epsilon.alt$
#let dt = $d t$
// macros

#show "tq": [tal que]
#show "tsq": [tales que]
#show "Hs": [espacio de Hilbert]
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

= Demostraciones de la Desigualdad de Khintchine

Version de @Tomczak-Jaegermann1989
#theorem[Desigualdad de Khintchine][
  Sea $1 <= p < infinity$. Entonces existen constantes positivas $A_p$ y $B_p$ tsq para toda sucesión de escalares ${a_i}$ uno
  tiene que
  $
    A_p (sum_i abs(a_i)^2)^(1/2) <= (integral_0^1 abs(sum_i r_i (t) a_j)^p d t)^(1/p) <= B_p (sum_i abs(a_i)^2)^(1/2).
  $
  Más aún, $B_p <= p^(1/2)$
]
#proof[
  Mostraremos primero el resultado para enteros. Sea $p in NN$ y $y in RR$, notemos que $abs(y)^p < p! (1 + abs(y)^p slash p!) <= p! e^abs(y)$.
  Por lo cual, definiendo $f(t) = sum_(n <= m) a_n r_(n)(t)$, entonces se cumple que 
  $
    norm(f)_p^p = integral_0^1 abs(f(t))^p dt <= p! integral_0^1 e^abs(f(t)) dt <= p! integral_0^1 (e^f(t) + e^(-f(t)) ) dt.
  $
  Podemos normalizar $f$ de tal forma que $norm(f)_2 = (sum_(n<=m) a_n^2)^(1/2) = 1$,
  luego, notemos que 
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
  Para $2<= p < infinity$, por la monotonía de las normas $L_p$ se puede concluir, para $a_1, dots, a_m in RR$ arbitrarios, que
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

  Ahora, para el caso $ 0 < p < 2$. Sea $theta = (2-(p/2))^(-1)$, podemos notar que $0 < theta < 1$, asi $1/theta > 1$ y su conjugado es $1/(1-theta)$, ademas $p theta + 4(1-theta) = 2$, por lo cual aplicando la desigualdad de Hölder se cumple que 
  $
    integral_0^1 abs(f(t))^2 dt = integral_0^1 abs(f(t))^(p theta) abs(f(t))^(4 (1 - theta)) dt &<= (integral_0^1 (abs(f(t))^(p theta))^(1/theta) dt)^theta (integral_0^1 abs(f(t))^(4 (1 - theta))^(1/(1-theta)) dt)^(1-theta) \
                            &= (integral_0^1 (abs(f(t))^p dt)^theta (integral_0^1 abs(f(t))^4 dt)^(1-theta),
  $
  lo cual se puede reescribir como $norm(f)_2^2 <= norm(f)_p^(p theta) norm(f)_4^(4(1-theta))$.
  Por lo probado anteriormente tenemos que $norm(f)_4 <= B_4 norm(f)_2$, por lo cual 
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
  como $1 - 2slash p theta = 2 - 4slash p$, vemos que $B_4^(2 - 4slash p) norm(f)_2 <= norm(f)_p$. Luego, por la monotonía obtenemos que $B_4^(2 - 4slash p) norm(f)_2 <= norm(f)_p <= norm(f)_2$.
]

Version que se encuentra en @Garling_2007
#theorem[Desigualdad de Khintchine][
  Existen constantes $A_p$ y $B_p$, para $0 < p < infinity$, tq si $a_1, dots, a_N$ son números reales y $epsa_1, dots, epsa_N$ son
  rvs Bernoulli, entonces
  $
    A_p norm(s_N)_p <= sigma <= B_p norm(s_N)_p,
  $
  donde $s_N = sum_(n=1)^N epsa_n a_n$ y $sigma^2 = norm(s_N)_2^2 = sum_(n=1)^N a_n^2$
]


= Demostraciones de la Desigualdad de Grothendieck.

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
