#import "@preview/touying:0.6.1": *
#import "@preview/datify:1.0.0"
#import "../themes/university.typ": *
#import "../definitions.typ": *
#import "@preview/theorion:0.4.1": *
#import cosmos.clouds: *


#let date = datetime(day: 10, month: 12, year: 2025)

#show: apply_definitions
#show: show-theorion

#show: university-theme.with(
  aspect-ratio: "4-3",
  config-info(
    title: [Un collage sobre la desigualdad de Grothendieck],
    subtitle: [Seminario de titulación I],
    author: [Antonio Barragán Romero \ Maite Fernández Unzueta],
    date: datify.custom-date-format(date, lang: "es"),
    logo: emoji.leaf.herb,
  ),
  header-right: self => box(utils.display-current-heading(level: 1)) + h(.3em) + self.info.logo,
  config-common(frozen-counters: (theorem-counter,)),
)

#show math.equation.where(block: false): box


#set par(justify: true)
#set text(lang: "es")
#let theorem = theorem.with(fill: rgb("#1b7491aa"))
// #set math.equation(numbering: "(1)")
#title-slide(
  authors: (
    [
      Antonio Barragán Romero. \
      #link("mailto:antonio.barragan@cimat.mx")
    ],
    [
      Maite Fernández Unzueta. \
      #link("mailto:maite@cimat.mx")
    ],
  ),
  logo: none,
)

= Introducción

==
El objetivo de este trabajo es presentar la demostración de un resultado fundamental de la Teoría de Operadores en
espacios de Banach, conocido como la _Desigualdad de Grothendieck_. Este resultado ha tenido un gran impacto en las
matemáticas, como muestran sus múltiples aplicaciones en distintas áreas de las matemáticas, como el análisis armónico,
la teoría de la computación o la optimización.

= Desigualdad de Khintchine

==

#theorem(title: "Desigualdad de Khintchine")[
  Para todo $0 < p < infinity$ existen constantes positivas $A_p$ y $B_p$ tsq para toda sucesión de escalares
  ${a_n} in l_2$ se cumple que
  $
    A_p (sum_n abs(a_n)^2)^(1/2) <= (integral_0^1 abs(sum_n r_n (t) a_n)^p dt)^(1/p) <= B_p (sum_n abs(a_n)^2)^(1/2)
  $
]<Khintchine_inequality>
*Observaciones*
-
// #slide(repeat: 3, self => [
//   #let (uncover, only, alternatives) = utils.methods(self)

//   At subslide #self.subslide, we can

//   use #uncover("2-")[`#uncover` function] for reserving space,

//   use #only("2-")[`#only` function] for not reserving space,

//   #alternatives[call `#only` multiple times \u{2717}][use `#alternatives` function #sym.checkmark] for choosing one of
//   the alternatives.
// ])


// #slide()[
//   *Demostración:*

//   - Se prueba para enteros y después se utiliza la monotonía de las normas $L_p$. Tomemos $p$ un entero.
//   #pause
//   - Basta considerar $a_1, dots, a_m$ finitos.
//   #pause
//   - Dados $a_1, dots, a_m$ utilizar las funciones de Rademacher $r_n in L[0, 1]_p$ para definir
//     $
//       f(t) := sum_(n <= m) a_n r_(n)(t)
//     $
//   #pause
//   - Acotar $f$ usando $abs(y)^p <= p!(1 + abs(y)^p slash p!) <= p! e^abs(y)$ para así acotar su norma
//     $
//       norm(f)_p^p = integral_0^1 abs(f(t))^p dt <= p! integral_0^1 e^abs(f(t)) dt <= p! integral_0^1 (e^f(t) + e^(-f(t)) ) dt.
//     $
//   #pause
//   - Normalizamos $f$ por su norma $L_2$ tq $norm(f)_2 = (sum_(n <= m) a_n^2 )^(1 slash 2) = 1$
//   #pause
//   - Estimar la cota de *falta algo* usando la independencia de las $r_n$ y lo anterior
//     $
//       p! integral_0^1 e^(f(t)) dt <= p! e^(1 slash 2),
//     $
//     así $norm(f)_p^p <= 2 p! e^(1 slash 2)$.
//   #pause
//   - En general para $a_1, dots, a_m$ y $2<=p<infinity$, sea $g(t) = sum_(n<=m) a_n r_(n)(t)$ y definamos
//     $f(t) = g(t)/norm(g)_2$, así $norm(f)_2 = 1$ y por lo anterior y la monotonía de las normas obtenemos
//     $
//       norm(g)_2 <= norm(g)_p <= 2 ceil(p)!e^(1 slash 2) norm(g)_2
//     $
//   #pause
//   - Para $0 < p < 2$ usar Holder con $0 < theta<1$ tq $theta = 1 slash (2 - p slash 2)$ y usando el caso $p=4$ para
//     obtener
//     $
//       B_4^(2 - 4 slash p) norm(g)_2 <= norm(g)_p <= norm(g)_2
//     $
// ]

#slide(repeat: 7, self => [
  #let (only, uncover, alternatives) = utils.methods(self)
  #let only_uncover(range, rest) = {
    only(range)[
      #uncover(range)[
        #rest
      ]
    ]
    // uncover(range)[
    //     #rest
    // ]
  }
  #proof[
    #only_uncover("1-4")[
      - Se prueba para enteros y después se utiliza la monotonía de las normas $L_p$. Tomemos $p$ un entero.
    ]
    // #pause
    #only_uncover("2-4")[
      - Basta considerar $a_1, dots, a_m$ finitos.
    ]
    // #pause
    #only_uncover("3-4")[
      - Dados $a_1, dots, a_m$ utilizar las funciones de Rademacher $r_n in L[0, 1]_p$ para definir
        $
          f(t) := sum_(n <= m) a_n r_(n)(t)
        $
    ]
    #only_uncover("4")[
      - Acotar $f$ usando $abs(y)^p <= p!(1 + abs(y)^p slash p!) <= p! e^abs(y)$ para así acotar su norma
        $
          norm(f)_p^p = integral_0^1 abs(f(t))^p dt <= p! integral_0^1 e^abs(f(t)) dt <= p! integral_0^1 (e^f(t) + e^(-f(t)) ) dt.
        $
    ]

    #only_uncover("5-7")[
      - Normalizamos $f$ por su norma $L_2$ tq $norm(f)_2 = (sum_(n <= m) a_n^2 )^(1 slash 2) = 1$
    ]
    #only_uncover("6-7")[
      - Estimar la cota de *falta algo* usando la independencia de las $r_n$ y lo anterior
        $
          p! integral_0^1 e^(f(t)) dt <= p! e^(1 slash 2),
        $
        así $norm(f)_p^p <= 2 p! e^(1 slash 2)$.
    ]
    #only("7-7")[
      - En general para $a_1, dots, a_m$ y $2<=p<infinity$, sea $g(t) = sum_(n<=m) a_n r_(n)(t)$ y definamos
        $f(t) = g(t)/norm(g)_2$, así $norm(f)_2 = 1$ y por lo anterior y la monotonía de las normas obtenemos
        $
          norm(g)_2 <= norm(g)_p <= 2 ceil(p)!e^(1 slash 2) norm(g)_2
        $
    ]
    #only("7-")[
      - Para $0 < p < 2$ usar Holder con $0 < theta<1$ tq $theta = 1 slash (2 - p slash 2)$ y usando el caso $p=4$ para
        obtener
        $
          B_4^(2 - 4 slash p) norm(g)_2 <= norm(g)_p <= norm(g)_2
        $
    ]
  ]
])
= Desigualdad de Grothendieck

==
#theorem(title: "Desigualdad de Grothendieck")[
  Existe una constante universal $K_G$ para la cual, dado cualquier Hs $H$, cualquier $n in NN$, y cualquier matriz
  escalar $(a_(i j))$ y cualesquiera vectores en $x_1, dots, x_n, y_1, dots, y_n in B_H$, tenemos que
  $
    abs(sum_(i, j) a_(i j) ip(x_i, y_j)) <= K_G max{ abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1}.
  $
]

*Observaciones*
- Como siempre consideramos una cantidad finita de elementos en $H$, basta que $H$ sea separable, sea ${e_n}_n$ su
  conjunto ortogonal numerable.
#slide(repeat: 10, self => [
  #let (only, uncover, alternatives) = utils.methods(self)
  #let only_uncover(range, rest) = {
    only(range)[
      #uncover(range)[
        #rest
      ]
    ]
    // uncover(range)[
    //     #rest
    // ]
  }
  #proof[
    #only("1-2")[
      - Por simplicidad definir
        $
          norm(a) = max{ abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1}
        $
        $
          triple(a) = abs(sum_(i, j) a_(i j) ip(x_i, y_j))
        $
    ]
    #only("2")[
      - Dado $x in H$, entonces $x = sum_(n=1)^infinity ip(x, e_n)e_n$ y usar los coeficiente para definir
        $
          X(t) := sum_(n=1)^infinity ip(x, e_n)r_(n)(t)
        $
    ]
    #only("3-4")[
      - Por la ortogonalidad de las funciones de Rademacher se cumple que:
        $
          norm(X)_2 = norm(x) wide "y" wide ip(x, y) = integral_0^1 X(t)Y(t)dt
        $
    ]
    #only_uncover("4-4")[
      - Acotar $X$, para ello tomamos $M>0$ y definimos
        $
          xl(t) = cases(X(t) &"si" abs(X(t)) <= M, M sign(X(g)) &"si" abs(X(t))>M)
        $
        $
          xu(t) = X(t) - xl
        $
        Notar que $abs(xl(t))<=M$ y $abs(xu(t)) <= abs(X(t)) - M$.
    ]
    #only_uncover("5-6")[
      - Aplicando la desigualdad $s <= m + s^2 slash 4m$, $s, m >0$ obtenemos que
        $
          abs(xu(t)) <= abs(X(t))^2 /(4M)
        $

    ]
    #only_uncover("6")[
      - Aplicar @Khintchine_inequality con $B_4 <= 3^(1slash 4)$ para obtener para $x in B_H$
      $
        abs(xu) <= sqrt(3)/(4M)
      $

    ]
    #only_uncover("7-8")[
      - Notar que $X Y = xl yl + (xu yl + X yu)$ asi por la desigualdad del trianguló
        $
          abs(sum_(i, j) a_(i j) ip(x_i, y_i)) &= abs(integral_0^1 sum_(i, j) a_(i, j) xi(t) yj(t) dt) \
          \
          & <= abs(integral_0^1 sum_(i, j) a_(i, j) xl_i (t) yl_j (t) dt) + \ & space space space abs(integral_0^1 sum_(i, j) a_(i, j) xu_i (t) yl_j (t)) + abs(integral_0^1 sum_(i, j) a_(i, j) X(t)yu_j (t) dt)
        $
        Acotamos cada sumando del lado derecho.
    ]
    #only_uncover("8")[
      - Usar que $abs(xl_(i)(t)), abs(xl_(i)(t))<=M$ para obtener
        $
          abs(integral_0^1 sum_(i, j) a_(i, j) xl_i (t) yl_j (t) dt) <=M^2 abs(integral_0^1 sum_(i, j) a_(i, j) dt) <= M^2 norm(a).
        $
    ]
    #only_uncover("9-10")[
      - Normalizar cada sumando $xu_i$, $yu_j$ y aplicar que $norm(xu_i)<= sqrt(3)/(4M)$ y se cumple que
        $
          abs(integral_0^1 sum_(i, j) a_(i, j) xu_i (t) yl_j (t)) <= sqrt(3)/(4M) triple(a) \
          abs(integral_0^1 sum_(i, j) a_(i, j) X(t)yu_j (t) dt) <= sqrt(3)/(4M) triple(a)
        $
    ]
    #only_uncover("10")[
      - Entonces se cumple
        $
          abs(sum_(i, j) a_(i j) ip(x_i, y_i)) <= M^2 norm(a) + sqrt(3)/(2M) triple(a)
        $
        y por tanto
        $
          triple(a) <= (2M^3)/(2M - sqrt(3)) norm(a).
        $
    ]
  ]

])

= Usos y aplicaciones


#bibliography("../biblio.yml")

#slide()[
  #set text(size: 16pt)
  // #bibliography("biblio.yml", full: true)
]
