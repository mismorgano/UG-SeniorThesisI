#import "@preview/ctheorems:1.1.3": thmbox, thmrules



// config
#set page(paper: "a4")
#set text(lang: "es", font: "New Computer Modern", size: 12pt)
#set heading(numbering: "1")

#set cite(form: "prose", style: "alphanumeric")
#show cite: set text(blue)

#show: thmrules
// envs
#let theorem = thmbox("theorem", "Teorema")

// functions
#let ip(x, y) = $angle.l #x, #y angle.r$
#let l = $cal(l)$
// macros

#show "tq": [tal que]
#show "tsq": [tales que]
#show "Hs": [espacio de Hilbert]

// layout

#align(center)[
  #text(size: 18pt)[
    Un Collage de la desigualdad de Grothendieck
  ]
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
