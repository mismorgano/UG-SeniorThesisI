#import "@preview/ctheorems:1.1.3": thmbox, thmproof, thmrules
#import "@preview/itemize:0.2.0" as el
#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "../definitions.typ": *


// config
#set page(paper: "a4", numbering: "1")
#set text(lang: "es", font: "New Computer Modern", size: 12pt)
#set heading(numbering: "1.")
#set par(justify: true)

#set cite(form: "prose", style: "alphanumeric")
#show cite: set text(blue)
#show heading.where(level: 1): it => {
  set text(size: 16pt)
  pagebreak(weak: true)
  it
}

#set math.equation(numbering: "(1)", supplement: [Eq])

#show: thmrules
#show: el.default-enum-list
#show: el.config.ref
#show: apply_definitions
// envs
#let definition = thmbox("definition", "Definición", inset: 0em)
#let theorem = thmbox("theorem", "Teorema", inset: 0em)
#let proposition = thmbox("proposition", "Proposición", inset: 0em)
#let proof = thmproof("proof", "Demostración", inset: 0em)


// layout

#align(center)[
  #text(size: 18pt)[
    Un collage de la desigualdad de Grothendieck
  ]


  #v(1cm)

  #grid(columns: (1fr, 1fr))[
    Maite Fernández Unzueta. \
    #link("mailto:maite@cimat.mx")
  ][
    Antonio Barragán Romero. \
    #link("mailto:antonio.barragan@cimat.mx")

  ]
  #v(3cm)
  #text(size: 14pt)[
    *Abstract*:
  ]
]

#outline()


= Introducción

El objetivo de este trabajo es presentar la demostración de un resultado fundamental de la Teoría de Operadores en
espacios de Banach, conocido como la _Desigualdad de Grothendieck_. Este resultado ha tenido un gran impacto en las
matemáticas, como muestran sus múltiples aplicaciones en distintas áreas de las matemáticas, como el análisis armónico,
la teoría de la computación o la optimización.


ha tenido un gran impacto en las matemáticas, que se ve reflejado en suso son A. Grothendieck presenta esta desigualdad
bajo el nombre de "théorème fondamental de la théorie métrique des produits tensoriels", dentro de su artículo publicado
en 1956 y titulado "Résumé de la théorie métrique des produits tensoriels topologiques" @ResumeMR94682.


En su trabajo "Résumé de la théorie métrique des produits tensoriels topologiques" @ResumeMR94682, Grothendieck hace un
desarrollo de normas tensoriales, normas-$tensor$, previo al enunciado y demostración de lo que él llamo "théorème
fondamental de la théorie métrique des produits tensoriels". El objetivo del presente trabajo es entender porque ese
teorema fundamental tiene como resultado una desigualdad entre matrices, la famosa _Desigualdad de Grothendieck_.

Es por ello
// Incluso el mismo menciona que se podia haber prescindido de tal desarrollo para formular y demostrar los resultado
// importantes de su "Résumé", más sin embargo es a través de tales desarrollos preliminares que se puede no solo formular
// de una manera concisa y sugerente sino también captar las relaciones entre las distintas variantes del "théorème
// fondamental" y tener una verdadera comprensión de la teoría.

Es por ello que nosotros también daremos una pequeña introducción a tales preliminares.

= Preliminares

== Formas Bilineales y Lineales

#definition([Mapeos Bilineales])[
  Dados $X, Y, Z$ Vss sobre el mismo campo $KK = RR space"o"space CC$, decimos que un mapeo
  $
    b:X times Y -> Z,
  $
  es bilineal si los mapeos sección
  // #let mtext = text.with(font: "Libertinus Serif")
  // $
  //   attach(bl: x, Phi) : & F & --> & G         & wide #mtext[and] wide Phi_y : & E & --> & G \
  //                        & y & ~~> & Phi(x, y) &                               & x & ~~> & Phi(x, y)
  // $

  $
    seci(b, x): & Y &            --> & Z       & wide "y" wide secd(b, y): & X &            --> & Z \
                & y & arrow.bar.long & b(x, y) &                           & x & arrow.bar.long & b(x, y)
  $
  son lineales para todo $x in X$ y todo $y in Y$,
]

Denotamos por $B(X, Y: Z)$ al conjunto de todos los mapeos bilineales de $X times Y$ a $Z$. En espacial, si $Z = KK$
simplemente escribimos $B(X, Y)$,

#proposition[
  Si $X, Y$ son Vss. Entonces existe un isomorfismo lineal entre los siguientes espacios $B(X, Y)$ y
  $L(X, Y')$
]
#proof[
  Sea $Phi: B(X, Y) -> L(X, Y')$ dada por
  $
    Phi: B(X, Y) & -> L(X, Y') \
     b(dot, dot) & -> T_b: X -> Y' \
                 &                 & x -> b(x, dot)
  $
  Veamos que $Phi$ es lineal, inyectiva y sobreyectiva. Notemos que $Phi(lambda b + d) = T_(lambda b + d)$, donde para
  todo $x in X$ se tiene que
  $
    T_(lambda b + d)(x) = lambda b(x, dot) + d(x, dot) = lambda T_b(x) + T_d(x),
  $
  por lo cual $Phi(lambda b + d) = lambda T_b + T_d$. Notemos que es inyectiva pues
  $
    ker Phi & = {b in B(X, Y): Phi(b) = 0} \
            & = {b in B(X, Y): b(x, dot) = 0, "para todo" x in X} \
            & = {b in B(X, Y): b(x, y) = 0, "para todo" x in X, "para todo" y in Y} \
            & = {b in B(X, Y): b = 0} = {0},
  $
  por lo cual $Phi$ es inyectiva. Ahora, si $T in L(X, Y')$, consideremos $b: X times Y -> KK$ dada por
  $b(x, y) = T(x)(y)$, notemos que si fijamos $x in X$ se tiene que $b(x, dot)$ es lineal pues $T(x)$ lo es, dado que
  $T in L(X, Y')$, es decir su imagen es un funcional lineal. Ahora si fijamos $y in Y$ notemos que $b(dot, y)$ también
  es lineal pues $T$ es lineal. Por ultimo notemos que, para todo $x in X$,
  $
    Phi(b)(x) = b(x, dot) = T(x)(dot),
  $
  por lo cual $Phi(b) = T$. Por todo lo anterior tenemos que $Phi$ es un isomorfismo lineal.
]

Más aún, tenemos que si $X, Y, Z$ son Vss se tiene que $B(X, Y; Z) iso L(X, L(Y, Z))$.

Por otro lado si $X, Y$ son Vss de dimensión finita, podemos fijar bases en cada uno y ver como actúa $Phi$ en alguna
$b in B(X, Y)$. Sean $e_1, dots, e_n$ y $f_1, dots, f_m$ bases de $X$ y $Y$, respectivamente, y sea $b in B(X, Y)$, como
$Phi(b) = T_b in L(X, du(Y))$ existe una matriz única que representa $T_b$ en las bases $e_1, dots, e_n$ y
$du(f_1), dots, du(f_m)$

Ahora bien si $b in B(X, Y)$ tenemos que
$
  b(sum_(i=1)^n x_i e_i, sum_(j=1)^m y_j f_j) &= sum_(i=1)^n x_i b(e_i, sum_(j=1)^m y_j f_j) = sum_(i=1)^n x_i ( sum_(j=1)^m y_j b(e_i, f_j)) \
  &= sum_(i=1)^n sum_(j=1)^m x_i y_j b(e_i, f_j) = sum_(j=1)^m sum_(i=1)^n x_i y_j b(e_i, f_j) \
  &= sum_(j=1)^m y_j (sum_(i=1)^n x_i b(e_i, f_j)),
$
de lo anterior podemos notar que $b$ solo depende de $b(e_i, f_j)$, es decir, solo depende de los valores en la base.
Por otro lado si $A=[b(e_i, e_j)] in #M _(n times m)$, podemos notar entonces que
$b(sum_(i=1)^n x_i e_i, sum_(j=1)^m y_j f_j) = y^t A^t x$, donde $x = vec(x_1, dots.v, x_n)$ y
$y = vec(y_1, dots.v, y_m)$ dados por los isomorfismos $i_X: X -> KK^n$, $i_Y: Y -> KK^m$, inducidos por sus bases.

Ademas, si $A = [b(e_i, f_j)] in #M _(n times m)$, es claro que $A^t (dot) = A^t circle.tiny i_X in L(X, Y)$, dadas unas
bases de $X$ y $Y$.

== Continuidad de formas Bilineales

Dada una $b in B(X, Y)$, podemos normar a $X times Y$ y como $KK$ es normado, podemos preguntarnos cunado se cumple que
$b$ es continua. Para ello tenemos que podemos hacer $X times Y$ un Vs,
$(x_1, x_2) + (y_1, y_2) = (x_1 + y_1, x_2 * y_2)$ y $lambda(x, y) = (lambda x, lambda y)$. Entonces al igual que con
$X$ o con $Y$, queremos dotar a $X times Y$ con una norma tq $X times Y$ sea un espacio vectorial topológico y dicha
norma sea continua respecto a la topología de $X times Y$. Como $X$, $Y$ son normados tienen una topología entonces
podemos considerar la topologia producto en $X times Y$.#footnote[¿Qué normas coinciden con la topología producto?] Para
ello notemos que:
$
  b(x, y) - b(x_0, y_0) & = b(x - x_0, y - y_0) + b(x - x_0, y_0) + b(x_0, y -y_0).
$<bilinear_continuous_identity>

#proposition[
  Si $b in B(X, Y)$ la siguientes afirmaciones son equivalentes:
  + $b$ es continua.<bilinear_continuous>
  + $b$ es continua en $(0, 0)$.<bilinear_continuous_at_zero>
  + $b$ es _acotada_, es decir, existe $C > 0$ tq $abs(b(x, y)) < C norm(x) norm(y)$.<bilinear_bounded>
]<continuity_of_bilinear_forms>
Notemos que si $b$ es continua en $(0, 0)$ entonces tenemos que dado $epsilon >0$ existe $delta > 0$ tq si
$norm((x, y) - (0, 0)) = norm((x, y)) <= delta$ entonces $abs(b(x, y) - b(0, 0))= abs(b(x, y)) < epsilon$. Asi, dado
$(x, y) in X times Y$ tenemos que $norm(delta ((x, y)) / norm((x, y))) = delta$ y por tanto
$abs(b(delta ((x, y)) / norm((x, y)))) = abs(b(delta x / norm((x, y)), delta y / norm((x, y)))) = delta^2 / norm((x, y))^2 abs(b(x, y)) < epsilon$,
lo cual implica que $abs(b(x, y)) < epsilon/delta^2 norm((x, y))^2$

#proof[
  #let xn = $accent(x_n, tilde)$
  #let yn = $accent(y_n, tilde)$
  @bilinear_continuous $=>$ @bilinear_continuous_at_zero Es claro por definición.

  @bilinear_continuous $arrow.l.double$ @bilinear_continuous_at_zero Se sigue pues $X times Y$ es lineal.

  @bilinear_continuous_at_zero $=>$ @bilinear_bounded Procedamos por contrapositiva. Entonces existe una sucesión
  $(x_n, y_n)$ tq $abs(b(x_n, y_n)) > n^2 norm(x_n) norm(y_n)$. Si consideramos $accent(x_n, tilde) = 1/n x_n/norm(x_n)$
  y $accent(y_n, tilde) = 1/n y_n /norm(y_n)$, podemos notar que $accent(x_n, tilde) -> 0$ y que
  $accent(y_n, tilde) -> 0$ por lo cual $(accent(x_n, tilde), accent(y_n, tilde)) -> (0, 0)$ en la topología producto y
  por tanto en norma. Sin embargo notemos que
  $
    abs(b(xn, yn)) = abs(1/n^2 1/(norm(x_n) norm(y_n)) b(x_n, y_n)) = 1/n^2 1/(norm(x_n) norm(y_n)) abs(b(x_n, y_n)) > 1,
  $
  por lo cual $b$ no es continua en $(0, 0)$.

  @bilinear_bounded $=>$ @bilinear_continuous Si $(x_n, y_n)$ es tq $(x_n, y_n) -> (x, y)$ cuando $n-> infinity$
  entonces tenemos que existe básico tq contiene la cola de $(x_n - x, y_n - y)$, por lo cual podemos escoger básicos de
  $x_n - x$ y $y_n - y$ $0$ del mismo radio tsq contienen la cola de $(x_n - x)$ y $(y_n - y)$, respectivamente, es
  decir se tiene que $x_n -> x$ y $y_n -> y$. De @bilinear_continuous_identity podemos notar que:
  $
    abs(b(x_n, y_n) - b(x, y)) & = abs(b(x_n - x, y_n - y) + b(x_n - x, y) + b(x, y_n -y)) \
                               & <= abs(b(x_n - x, y_n - y)) + abs(b(x_n - x, y)) + abs(b(x, y_n -y)) \
                               & <=C norm(x_n- x) norm(y_n - y) + C norm(x_n - x)norm(y) + C norm(x)norm(y_n - y),
  $
  y por tanto $b(x_n, y_n) -> b(x, y).$

]

Ahora bien, si $X, Y$ son Nss, como vimos $B(X, Y)$ es un Vs al igual que $L(X, du(Y))$ y por tanto podemos normar estos
espacios si $b in B(X, Y)$
$
  norm(b) = sup { abs(b(x, y)): norm((x, y)) <= 1} = sup{abs(y^t A^t x): norm((x, y)) <= 1},
$
y si $T in L(X, du(Y))$ entonces
$
  norm(T) = sup{norm(T(x)): norm(x)<=1} = sup{sup{abs(T(x)(y)): norm(y) <=1}: norm(x)<=1},
$
más aún, por @continuity_of_bilinear_forms podemos dotar a $B(X, Y)$ con la norma
$
  norm(b) = inf{ C> 0: abs(b(x, y)) < C, "para" x in B_X, y in B_Y}.
$
luego
$
  norm(Phi(b)) & = sup{norm(T_(b)(x)): norm(x)<=1} = sup{sup{abs(T_(b)(x)(y)): norm(y) <=1}: norm(x)<=1} \
               & =
$

== Productos tensoriales

Los preliminares del trabajo de Grothendieck son para normar el producto tensorial de dos espacios vectoriales, por lo
cual es indispensable no solo definirlos sino también ver algunas de sus propiedades básicas.

El objetivo principal de los productos tensoriales es linealizar mapeos bilineales, en el sentido de que $L(V, Z)$ y
$B(X, Y semi Z)$ sean isomorfismos. Lo anterior se expresa mejor con la siguiente propiedad universal del producto
tensorial, y por tanto dados $X$, $Y$ Vss podemos hablar _de su_ producto tensorial de manera única.

#definition([Producto tensorial #footnote[Como se muestra en @DefantFloretMR1209438]])[
  Sean $X, Y$ Vss sobre el mismo campo $KK$. El _*producto tensorial*_ $(X tensor Y, tensor)$ es un par, donde
  $X tensor Y$ es un $KK$-Vs y $tensor in Bil(X, Y, X tensor Y)$ es tq para todo $KK$-Vs $G$ y todo
  $Phi in Bil(X, Y, G)$ existe un único $U in L(T, G)$ tq $Phi = U ct tensor$, es decir, el siguiente diagrama conmuta.
  #align(center, diagram(
    $
                                 X times Y edge("d", tensor, ->) edge(Phi, ->) & G \
      X tensor Y edge("tr", U, label-anchor: "west", label-sep: #(-0.4em), ->)
    $,
  ))
]

La construcción del producto tensorial es como sigue. Sean $X, Y$ dos Vss. Dados $x in X$, $y in Y$ definimos
$x tensor y in B(X, Y)'$ como
$
  (x tensor y) (A) = A(x, y), wide "para todo" A in B(X, Y).
$
Entonces $X tensor y := span{x tensor y: x in X, y in Y}$.

=== Normas razonables y cruzadas

Nos interesa normar el espacio $X tensor Y$.

Como menciona @SchattenMR36935 nos interesan las normas que cumplan lo siguiente.
#definition[_norma cruzada_][
  Una norma $alpha$ sobre $X tensor Y$ se dice cruzada si cumple que:
  $
    alpha(X tensor Y) = norm(x) norm(y)
  $
]

Grothendieck en su "Résumé" introdujo el termino de norma _razonable_ la cual cumple que es cruzada. A continuación
damos una una definición que es equivalente a la dada por Grothendieck.
#definition[_norma razonable_][
  Sean $X$ y $Y$ Bss (sobre el mismo campo). Una norma $alpha$ sobre $X tensor Y$ se dice _razonable cruzada_ si $alpha$
  satisface las siguientes condiciones:
  + para $x in X$ y $y in Y$, se debe cumplir
    $
      alpha(x tensor y) <= norm(x) norm(y),
    $
  + para $x^* in X^*$ y $y^* in Y^*$, $x^* tensor y^* in (X tensor Y, alpha)$, y
    $
      norm(x^* tensor y^*) <= norm(x^*) norm(y^*).
    $
]

Como menciona Grothendieck dado $X tensor Y$ existen una _menor norma razonable y cruzada_ y una _mayor norma razonable
y cruzada_

#definition[Norma Proyectiva][
  La norma proyectiva $pi$ sobre el producto tensorial $X tensor Y$ entre dos Nss $X$, $Y$ se define como:
  $
    pi(u) = inf{sum_(i=1)^n norm(x_i) norm(y_i): u = sum_(i=1)^n x_i tensor y_i}.
  $
]
#proposition[
  Sean $X$, $Y$ Bss. Entonces $pi$ es una norma sobre $X tensor Y$ y ademas $pi(x tensor y) = norm(x) norm(y)$, es
  decir, $pi$ es razonable cruzada.
]

Detonaremos por $X tensor_pi Y$ al producto tensorial $X tensor Y$ junto con la norma $pi$. Y denotamos a su
completación como $X hat(tensor)_pi Y$.

Notemos que dado $x in X$, $y in Y$ podemos definir $B_(x, y) in B(X', Y')$ dado por
$B_(x, y)(phi, psi) = phi(x)psi(y)$. Luego, por la propiedad universal del tp tenemos que existe mapeo único de
$X tensor Y$ a $B(X', Y')$ tq $x tensor y |-> B_(x, y)$, y por tanto tenemos un embedimiento
$X tensor Y subset B(X', Y')$. La norma inyectiva es la inducida por tal embedimiento.

#definition[Norma inyectiva][
  La norma inyectiva $epsilon$ sobre el producto tensorial $X tensor Y$ entre dos Nss $X$, $Y$ se define como:
  $
    epsilon(u) = sup{abs(sum_(i=1)^n phi(x_i)psi(y_i)): u = sum_(i=1)^n x_i tensor y_i, phi in B_X', psi in B_Y'}.
  $
]


= La Desigualdad de Khintchine

Primero veamos un resultado muy importante que nos permitirá después llegar a nuestro objetivo principal,
@Grothendieck_inequality. El siguiente resultado se base en las propiedades de la siguiente clase de funciones: las
*funciones de Rademacher*. Para cada $n in NN$ definimos $r_n:[0, 1]->RR$ definidas por
$
  r_n (t) = sign(sin(2^n pi t)),
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
  como las $r_n$ son Rvs independientes se cumple que
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
]

Version que se encuentra en @Garling_2007
#theorem[Desigualdad de Khintchine][
  Existen constantes $A_p$ y $B_p$, para $0 < p < infinity$, tq si $a_1, dots, a_N$ son números reales y
  $epsa_1, dots, epsa_N$ son Rvs Bernoulli, entonces
  $
    A_p norm(s_N)_p <= sigma <= B_p norm(s_N)_p,
  $
  donde $s_N = sum_(n=1)^N epsa_n a_n$ y $sigma^2 = norm(s_N)_2^2 = sum_(n=1)^N a_n^2$
]


= La Desigualdad de Grothendieck.

Ahora veamos la demostración del Teorema más importante, nuestro objetivo principal.

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
    abs(sum_(i, j) a_(i j) ip(x_i, y_j)) <= K_G max{ abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1}.
  $
]<Grothendieck_inequality>

Antes de seguir con la Demostración, notemos lo siguiente. Dado cualquier Hs $H$ y cualesquiera $s_i$, $t_j$ tsq
$abs(s_i) <= 1$, $abs(t_j) <= 1$, podemos escoger $h in H$ tq $norm(h) = ip(h, h) = 1$ y ademas dada la bilinealidad de
$ip(dot, dot)$ tenemos que $ip(s_i h, t_j h) = s_i t_j ip(h, h) = s_i t_j$ y ademas
$norm(s_i h) = abs(s_i)norm(h)=abs(s_i) <= 1$ por lo que $s_i in B_H$, de manera similar $t_j in B_H$. De lo anterior
podemos notar que
$
  { abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1} subset {abs(sum_(i, j) a_(i j) ip(x_i, y_i)): x_i in B_H, y_j in B_H},
$
por lo cual se cumple que:
$
  sup{ abs(sum_(i, j) a_(i, j) s_i t_j): abs(s_i) <=1, abs(t_j) <=1} <= sup {abs(sum_(i, j) a_(i j) ip(x_i, y_i)): x_i in B_H, y_j in B_H},
$
es decir, se cumple la desigualdad contraria.


#proof[
  
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

  Al igual que con la Demostración de @Khintchine_inequality la idea es es poder embeber cualquier Hs separable en
  $L_2[0, 1]$ que respete su producto interno. Para ello, de igual manera, utilizaremos las funciones de Rademacher
  ${r_n}_n$ las cuales formal un conjunto ortonormal en $L$. La forma en que lo haremos sera la siguiente: dado
  $x in H$, como $H$ tiene base ortonormal ${e_n}_n$ sabemos que $x = sum_n ip(x, e_n) e_n$ y ademas
  $infinity > norm(x) = sum_(n) ip(x, e_n)$, asi podemos definir $X:[0, 1] -> RR$ como
  $
    X(t) := sum_(n) ip(x, e_n)r_(n)(t).
  $
  Luego, por la ortonormalidad de las funciones de Rademacher tenemos que
  $
    norm(X)_2^2 = integral_0^1 X(t)^2 dt = integral_0^1 abs(sum_(n) ip(x, e_n)r_(n)(t))^2 dt = integral_0^1 sum_(n) ip(x, e_n)^2 dt = norm(x)^2,
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
  mas aun, usando la siguiente desigualdad $s<= m + (s^2)/(4m)$, con $s, m > 0$, tenemos que
  $
    abs(X(t)) <= M + (abs(X(t))^2)/(4M) ==> abs(xu(t)) <= abs(X(t))^2/(4M).
  $
  Por lo cual, si suponemos que $x in B_H$ y usando la @Khintchine_inequality obtenemos que
  $
    norm(xu)_2^2 = integral_0^1 abs(xu(t))^2 dt <= 1/(16M^2) integral_0^1 abs(X(t))^4 dt <= B_4^4/(16M^2) norm(x)_2^2 <= 3/(16M^2),
  $
  donde la ultimo desigualdad se da pues $B_4 <= 3^(1/4)$. Lo anterior implica que para $x in B_H$ se cumple que
  $norm(xu)_2 <= sqrt(3)/(4M)$. Por ultimo, primero notemos que $X = xu + xl$, por lo cual
  $X Y = (xu + xl)(yu + yl) = (xu + xl)(yl) + (X)(yu) = xl yl + (xu yl + X yu)$. Luego, si $x_1, dots, x_n$ y
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


#bibliography("../biblio.yml", full: true)
