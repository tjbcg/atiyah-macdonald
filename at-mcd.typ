#import "@preview/fletcher:0.5.3" as fletcher: diagram, edge, node
#import "@preview/quick-maths:0.2.1": shorthands
#set text(font: "New Computer Modern")
#set par(justify: true)
#set page(paper: "a4")
#set document(
  title: "Solution to exercises — Atiyah-Macdonald's Introduction to Commutative Algebra",
)

#let exocounter = counter("exo")
#let exo() = [*Exercise #exocounter.step(level: 2) #context exocounter.display((
    ..,
    num,
  ) => num).*]
#let skipexo() = exocounter.step(level: 2)

#set heading(numbering: (..n) => {
  if n.pos().len() < 2 {
    numbering("1.1", ..n)
  }
})

#show heading.where(outlined: true): it => {
  if it.level == 1 {
    exocounter.update(counter(heading).get() + (0,))
    set align(center)
    [Chapter #counter(heading).display() --- #it.body]
  } else {
    set text(size: 11pt)
    v(1cm)
    align(center, emph[#counter(heading).display() #it.body])
  }
}

// #show math.equation: box

#show regex("\biff\b"): "if and only if"
#show regex("\bSES\b"): "short exact sequence"
#show regex("\bES\b"): "exact sequence"
#show regex("\bLES\b"): "long exact sequence"

#set enum(numbering: "i)")

#let aa = $frak(a)$
#let bb = $frak(b)$
#let cc = $frak(c)$
#let pp = $frak(p)$
#let mm = $frak(m)$
#let qq = $frak(q)$
#let Spec = math.op("Spec")
#let Max = math.op("Max")
#let phi = sym.phi.alt
#let varphi = sym.phi
#let tens = sym.times.circle
#let iso = sym.tilde.eq
#let oplus = sym.plus.circle
#let MM = math.bold("M")
#let NN = math.bold("N")
#let RR = math.bold("R")
#let CC = math.bold("C")
#let ZZ = math.bold("Z")
#let QQ = math.bold("Q")
#let PP = math.bold("P")
#let Ann = math.op("Ann")
#let Frac = math.op("Frac")
#let Supp = math.op("Supp")

#show: shorthands.with(
  ($|-->$, sym.arrow.bar.long),
)

#let (injlim, projlim) = {
  let factory = arrowsym => context {
    let size = measure[lim].width
    let arrow = pad(top: -1em, math.stretch(math.script(arrowsym), size: size))
    math.attach(math.limits[lim], b: arrow)
  }
  (
    math.op(factory(sym.arrow.r), limits: true),
    math.op(factory(sym.arrow.l), limits: true),
  )
}

#align(center)[
  #set text(size: 14pt)
  #set text(weight: "bold")
  _Introduction to Commutative Algebra_

  Atiyah & Macdonald

  Solution to exercises
]

#outline()

= Rings and Ideals

#exo() Let $x$ be a nilpotent element of the ring $A$, and $n > 0$ an integer
such that $x^n = 0$. Then,
$ (1+x) sum_(i >= 0)^(n-1) (-1)^i x^i = 1. $
Therefore, $1+x$ is a unit. The sum of a nilpotent $x$ and a unit $u$ can be
written in the form $u (1+ u^(-1)x)$, which makes it again a unit since
$u^(-1) x$ is nilpotent.

#exo()
+ If $f$ is a unit in $A[x]$ then there is $g in A[x]$ such that $f g = 1$ and
  in turn $f(0) g(0)=1$, whence $f(0)$ is a unit in $A$. If
  $f = a_0 + a_1 x + dots.c + a_n x^n$ and $g = b_0 + b_1 x + dots.c + b_m x^m$
  is the inverse of $f$ in $A[x]$, then we shall prove by induction on $r$ that
  $a_n^(r+1)b_(m-r)=0$. Indeed, this is true for $r = 0$ (last coefficient of
  $f g$), and if it is true for $0 <= r < n + m - 1$, then taking the
  coefficient of degree $n+m-r-1$ in $f g =1$ and multiplying by $a_n^r$ yields
  $ sum_(i+j=n+m-r) a_n^r a_i b_j = 0 $
  and using the inductive hypothesis we can drop all summands with $j > m-r$,
  leaving only $a_n^(r+1) b_(m-r) = 0$.

  We get $a_n^(m+1) b_0 = 0$ but $b_0$ is a unit so $a^n$ is nilpotent. Thus,
  $f - a_n x^n$ is a unit as per the previous exercise, which implies by
  induction that all the nonconstant coefficients are nilpotent. The reciprocal
  property is immediate, since a sum of nilpotents is nilpotent and a unit plus
  a nilpotent is a unit.
+ If $f$ is nilpotent, $1+f$ is a unit (exercise 1) and as per the previous
  point, $a_1, dots.c, a_n$ are nilpotent, and $a_0 = f(0)$ is clearly
  nilpotent. The converse is clear as well (sum of nilpotents is nilpotent per
  the binomial formula).
+ Let $f$ be a zero divisor in $A[x]$ and $g$ be a least degree polynomial
  $b_0+ dots.c + b_m x^m$ such that $f g =0$. Then, $a_n b_m = 0$ hence
  $a_n g = 0$ since $f a_n g = 0$ and $a_n g$ has degree $< m= deg(g)$. Suppose
  $a_(n-r) g = 0$ for $r < n$. Then writing explicitely the coefficients of
  $f g = 0$, one finds
  $ f g = (a_0 + dots.c + a_(n-r-1) x^(n-r-1))g = 0 $
  thus $a_(n-r-1) b_m =0$ and $a_(n-r-1) g = 0$. We deduce $b_m f = 0$ (all the
  coefficients cancel).
+ Let $aa = (a_0, dots.c, a_n)$, $bb = (b_0, dots.c, b_n)$ and
  $cc = (a_0 b_0, a_1 b_0 + a_0 b_1, dots.c, a_n b_n)$. Clearly,
  $cc subset aa inter bb$, thus if $cc=(1)$ then $aa = bb = (1)$. Assume now
  that $aa=bb = (1)$. If $cc subset.neq (1)$, then there is a maximal ideal $mm$
  containing $cc$. The image $overline(f g)$ of $f g$ in $A slash mm [x]$ is
  $0$, thus $f$ and $g$ are zero divisors (they are both nonzero) in the
  integral domain $A slash mm [x]$, contradiction.

#skipexo()


#exo() The nilradical is contained in every prime ideal, thus in every maximal
ideal: $NN subset RR$. Then, let $f$ be an element of the Jacobson radical $RR$.
Then, $1- f x$ is a unit, therefore all the coefficients from $f x$ besides the
first one are nilpotent, that is, all the coefficients from $f$ are nilpotent
and therefore $f$ is nilpotent too.

#exo()
+ Let $f = sum_(n>=0) a_n x^n$ be an element of $A [[x]]$ with $a_0$ a unit in
  $A$. Take #h(1fr)
  $
    g = a_0^(-1)(1 - (a_0^(-1)f-1) + (a_0^(-1)f-1)^2 - (a_0^(-1)f-1)^3 + dots.c ).
  $
  This is a well-defined element of $A[[x]]$ since $f-a_0$ has only nonconstant
  monomial terms thus each coefficient of $g$ is defined only by a finite amount
  of terms in the infinite sum. We know from the theory of infinite series that
  $f g = 1$, which makes $f$ a unit. The converse is immediate.
+ Let $f$ be a nilpotent formal power series. For every prime ideal $pp$ of $A$,
  the image $f_pp$ of $f$ in $A slash pp [[x]]$ is null since that ring is
  integral and $f$ is nilpotent. Therefore, the coefficients of $f$ are in $pp$
  for every prime $pp$ of $A$. Since the nilradical is the intersection of all
  prime ideals, all the coefficients are nilpotent.
+ $f$ is in the Jacobson iff $1-f g$ is a unit for all $g in A[[x]]$ iff
  $1 - a_0 c$ is a unit for all $c in A$ iff $a_0$ is in the Jacobson of $A$.
+ $A[[x]] slash (x) = A$ whence the ideals of $A$ correspond (in an
  order-preserving way) to ideals of $A[[x]]$ containing $x$. Moreover, for all
  $f in A[[x]]$, $1 - x f$ is a unit (its constant coefficient is $1$),
  therefore $x$ is in the Jacobson radical and thus in every maximal ideal of
  $A[[x]]$. Thus, there is a bijection between maximal ideals $mm$ of $A [[x]]$
  and maximal ideals of $A$, given by $mm |-> mm^c$. Moreover, the extension
  $mm |-> mm^e$ is clearly $mm |-> (mm, x)$ (given by the canonical inclusion
  $A --> A[[x]]$).
+ Let $pp$ be a prime ideal in $A$, and denote by $pi$ the canonical quotient
  map $A [[x]] --> A [[x]] slash (pp, x)$. Elements of $A[[x]] slash (pp,x)$ are
  of the form $pi(a)$ for some $a in A$. Denote by $pi'$ the canonical map
  $A --> A slash pp$. The map
  $pi(a) in A[[x]] slash (pp, x) arrow.bar.long pi'(a) in A slash pp$ is well
  defined and defines an isomorphism. As such, $A [[x]] slash (pp, x)$ is an
  integral domain and $(pp, x)$ is a prime ideal, which concludes.

#exo() Suppose that the Jacobson is not contained in the nilradical. Then there
is a non-zero idempotent $e$ contained in the Jacobson but not in the
nilradical. Therefore, $e (1-e) = 0$ and $1 -e$ is a unit (because $e$ is in the
Jacobson), so $e = 0$ which is absurd.

#exo() Let $pp$ be a prime ideal of $A$, and let $x$ be an element outside $pp$.
There is $n > 1$ such that $x(1-x^(n-1))=0$, and since $A slash pp$ is an
integral domain, this relation yields $overline(x)^(n-1)=1$ in $A slash pp$.
Therefore, $A slash pp$ is a field (all non-zero elements have a multiplicative
order and thus are units), and $pp$ is maximal.

#exo() This is a straightforward application of Zorn's lemma. To build a lower
bound for each descending chain, take the intersection of the primes in that
chain, which is still prime thanks to the inclusion relation between primes in
the chain.

#exo() If $aa = r(aa)$ then we already know that $aa$ is the intersection of all
prime ideals containing $aa$ (Prop 1.14). If $aa = inter.big_i pp_i$ and
$x^n in aa$, then $x^n in pp_i$ for all $i$, thus $x in pp_i$ for all $i$ and
$x in aa$, whence $aa = r(aa)$.

#exo()
#[
  - $"i") => "iii")$ The nilradical of $A$ is the intersection of all of its
    prime ideals. Thus, $frak(N)$ is the sole prime ideal, making it maximal,
    and thus $A slash frak(N)$ is a field.

  - $"iii") => "ii")$ Let $a in A$ be a non-nilpotent element, so that
    $overline(a) != 0$ in $A slash frak(N)$ (which is a field). Take $b in A$ to
    be in the class of inverses of $overline(a)$: $overline(a b) = 1$ in
    $A slash frak(N)$. Then $a b = 1 + x$ for some nilpotent $x$, but the sum of
    a nilpotent and a unit is again a unit (Exercise 1.1), thus $a b$ is a unit
    and $a$ is a unit.

  - $"ii") => "i")$ Assume $pp$ is a prime ideal distinct from the nilradical
    $frak(N)$. Then $pp$ contains an element $x$ which is not nilpotent, and
    that makes it a unit by hypothesis. This is a contradiction, since a prime
    ideal can not contain units. Therefore, the nilradical is the only possible
    prime ideal, and one easily checks that it is.
]

#exo()
+ $(1+x)^2 = 1+x = 1 + 2x + x^2 = 1 + 2x + x ==> 2x = 0$.
+ Every prime is maximal (Exercise 1.7), therefore $A slash pp$ is a field. If
  $x in A slash pp$ is non-zero then $x = x^2 x^(-1) = x x^(-1) = 1$.
+ Let $a, b$ be elements of $A$. We have $a(a+b+a b) = a+2a b = a$ and
  $b(a + b + a b)=b + 2 a b = b$ so $(a, b) = (a + b + 2 a b)$. By induction,
  this shows that $A$ is a PID.

#exo() Say $A$ is local with maximal ideal $mm$ and $e$ is an idempotent
different from $0, 1$. We have that $e(e-1)=0$ whence $e$ is not a unit, meaning
$e in mm$. The maximal ideal is also the Jacobson radical, therefore $1-e$ is a
unit, which contradicts $e(e-1)=0$.

#skipexo()

#exo() Apply Zorn's lemma to show existence of maximal elements (take the union
of each term as the maximum of a chain). Let $S$ be maximal in $Sigma$,
$x, y in.not S$. If $x y in S$ then both $x$ and $y$ are zero divisors, meaning
$(x) + S$ and $(y) + S$ are in $Sigma$ which contradicts maximality of $Sigma$.
Thus, $x y in.not S$.

// == The prime spectrum of a ring

#exo()
+ If a prime ideal $pp$ contains $aa$, then it also contains $r(aa)$ since
  $r(aa)$ is an intersection of some primes, $pp$ included. The rest is clear.
+ Immediate.
+ If $pp$ contains all $E_i$ then $pp in inter.big_i V(E_i)$, and vice-versa.
+ $r(aa inter bb) = r(aa bb)=r(aa) inter r(bb)$

#exo()
- $Spec(ZZ) = {(0)} union {(p), p " prime"}$
- $Spec(RR) = {(0)}$
- $Spec(CC[x]) = {(0)} union {(x-a), a in CC}$

#exo() We first show that the principal opens form a basis for the Zariski
topology. If $U = X without V(aa)$ is an open subset then for any $f in aa$,
$X_f subset U$. Then,
$
  union.big_(f in aa) X_f = X without (inter.big_(f in aa) V(f)) = X without (V(union.big_(f in aa) (f))) = X without V(aa) = U .
$
which shows that the $(X_f)_(f in aa)$ form a basis for the Zariski topology.
+ $X_f inter X_g = X without (V(f) union V(g)) = X without V( (f g)) = X_(f g)$
+ $X_f = emptyset <==> V(f) = X <==> f in inter.big_(pp in Spec(A)) pp = frak(N)(A)$
+ $X_f = X <==> V(f)=0 <==> f$ is a unit (otherwise $(f)$ is a proper ideal
  contained in a prime maximal ideal).
+ $X_f = X_g <==> V(f) = V(g) <==> r((f)) = r((g))$
+ Every open covering of $X$ can be reduced to an open covering by basic open
  sets $X_f, f in I subset A$ (cover each open with basic open sets). We get
  $X = union.big_(f in I) X_f$ whence
  $ emptyset = inter.big_(f in I) V(f) = V( union.big_(f in I) (f) ) = V(I) $
  thus $r(I) = (1)$ and $I = (1)$. Thus, there is a finite relationship
  $ 1 = sum_(i=1)^n g_i f_i $
  with $f_i in I$. Thus, $X = union.big_(i=1)^n X_(f_i)$ which concludes.
+ $X_f = union.big_(f' in I) X_(f')$ yields
  $V(f) = inter.big_(f' in I) V(f') = V(I)$ whence $r((f)) = r(I)$ and
  $f^n = sum_(f' in J) g_(f') f'$ for $J$ a finite subset of $I$. The rest is
  the same as before since $f^n in pp <==> f in pp$ for any prime ideal $pp$.
+ If $U$ is quasi compact then since $U$ has an open cover of basic open sets,
  then it is a finite union of $X_f$. Conversely, if it is a finite union of
  $X_f$, $f in I$, and ${U_j}_(j in J)$ is another open cover, then each
  ${U_j inter X_f}_(j in J)$ is an open cover of $X_f$ which is quasi compact.
  Exctract the indices for a finite covering to yield a finite open covering of
  $U$ from the ${U_j}$.

#exo()
+ If $pp_x$ is maximal, then indeed ${x} = V(pp_x)$ which is closed. Conversely,
  if ${x}$ is closed, then there is no ideal $aa$ such that $pp_x subset aa$,
  meaning $pp_x$ is maximal.
+ $
    overline({x}) = inter.big_(Y " closed"\ x in Y)Y = inter.big_(f in A\ pp_x subset r(f)) V(f) = V(union.big_(f in A\ pp_x in r(f)) (f)) = V(pp_x)
  $
+ $y in overline({x}) <==> y in V(pp_x) <==> pp_x subset pp_y$
+ From previous point, either $X without overline({x})$ or
  $X without overline({y})$ works.

#exo() Assume $frak(N)(A)$ is not prime, i.e. there exists
$a, b in A without frak(N)(A)$ such that $a b$ is nilpotent. Then
$X_a inter X_b = X without (V(a) union V(b)) = X without V(a b)$, whence
$X_a inter X_b=emptyset$ since $X = V(frak(N)(A)) subset V(a b)$ (the nilradical
is contained in every prime ideal, and $a b in frak(N)(A)$). Note also that
neither $X_a$ nor $X_b$ is empty, since $a$ and $b$ are not nilpotent. Thus,
$Spec(A)$ is not irreducible.

Assume now that the nilradical is prime, and that $X_f, X_g$ are two basic open
sets with empty intersection: $X_f inter X_g = emptyset$. Thus,
$V(f) union V(g) = V (f g) = X$. In particular, $f g in frak(N)(A)$ and since
that ideal is prime, either $f$ or $g$ is nilpotent, which implies that one of
$X_f$ and $X_g$ is empty. Therefore, $Spec(A)$ is indeed irreducible.

#exo()
+ Open subsets of $overline(Y)$ are also open in $Y$, thus dense in $Y$, thus
  dense in $overline(Y)$.
+ Apply Zorn's lemma. To find a maximal element of a chain, take the closure of
  the union of the terms.
+ From i) the maximal irreducible subspaces are necessarily closed. Then, every
  point of $X$ is contained in the irreducible subspace $overline({x})$ and
  therefore in a maximal irreducible subspace. This shows that maximal
  irreducible subspaces cover $X$. In a Hausdorff space, since any two points
  can be separated by neighborhoods, the irreducible components are the
  singletons.
+ In $X = Spec(A)$, candidates are closed thus of the form $V(pp)$ for some
  prime ideal $pp$. Since $V(-)$ is inclusion-reversing, it will be sufficient
  to show that whenever $pp$ is prime, $V(pp)$ is irreducible (maximality will
  automatically ensue for minimal primes). Let $pp$ be such a prime and assume
  $V(pp)$ is not irreducible, that is, there are nonempty open subspaces $U, V$
  of $V(pp)$ with empty intersection: $U inter V = emptyset$. We can write
  $U = V(pp) without V(aa)$ and $V = V(pp) without V(bb)$ for some ideals
  $aa, bb$ containing $pp$ and we get
  $U inter V = emptyset = V(pp) without (V(aa) union V(bb)) = V(pp) without V(aa bb)$,
  whence $V(pp) subset V(aa bb)$ and $r(aa bb) subset pp$. Since
  $pp subset aa, bb$, we get $pp subset r(aa bb) subset pp$ thus
  $pp = r(aa bb) supset.eq aa bb$, which implies $aa subset.eq pp$ or
  $bb subset.eq pp$ since $pp$ is prime. Since we started with ideals containing
  $pp$, this means either $aa = pp$ or $bb = pp$, which contradicts the
  nonemptyness of $U$ and $V$.

  Note that this shows two things: irreducible components are of the form
  $V(pp)$ for $pp$ a minimal prime, and $V(pp)$ is always irreducible regardless
  of minimality, provided $pp$ is prime.

#exo() $phi : A --> B$ a ring homomorphism, $qq subset Y$ a prime ideal. Assume
$a b in phi^(-1)(qq)$, then $phi(a) phi(b) in qq$ so $phi(a) in qq$ or
$phi(b) in qq$ and thus $a$ or $b$ is in $phi^(-1)(qq)$, thus $phi^(-1)(qq)$ is
prime. Define $phi^* : Spec(B) --> Spec(A)$ as $qq |-> phi^(-1)(qq)$. Let
$X = Spec(A)$ and $Y = Spec(B)$.
+ If $f in A$ then #h(1fr)$
    phi^(*-1)(X_f) & = {y in Y | phi^*(pp_y) in X_f} \
                   & = {y in Y | f in.not phi^(-1)(pp_y)} \
                   & = { y in Y | phi(f) in.not pp_y } = X_(phi(f))
  $
  Preimages of open subsets are open subsets, making $phi^*$ continuous.
+ If $aa$ is an ideal of $A$ then
  $
    phi^(*-1)(V(aa)) & = { y in Y | aa subset phi^(-1)(pp_y)} \
                     & = { y in Y | phi(aa) subset pp_y } | \
                     & = { y in Y | B phi(aa) subset pp_y } \
                     & = {y in Y | aa^e subset pp_y} = V(aa^e)
  $
+ Let $bb$ be an ideal of $B$.
  $
    phi^(*)(V(bb)) & = { x in X | bb subset phi(pp_x) } subset.eq {x in X | phi^(-1)(bb) subset pp_x } = V(bb^c).
  $
  By closedness of $V(bb^c)$, $overline(phi^*(V(bb))) subset V(bb^c)$. There is
  an ideal $aa$ of $A$ such that $overline(phi^*(V(bb))) = V(aa)$ and
  $
    V(aa^e) = phi^(*-1)(V(aa)) = phi^(*-1)(overline(phi^*(V(bb)))) supset.eq V(bb)
  $
  so $aa^e subset r(bb)$ and $aa subset r(bb^c)$ whence
  $overline(phi^*(V(bb))) = V(aa) supset.eq V(bb)$.
+ If $phi$ is surjective, then it factors into an isomorphism
  $tilde(phi) : A slash ker(phi) --> B$ which has an inverse
  $tilde(psi) : B --> A slash ker(phi)$. Then clearly, $tilde(phi)^*$ is a
  homeomorphism (of continuous inverse $tilde(psi)^*$) of $Y$ onto
  $Spec(A slash ker(phi))$.

  There is a one-to-one correspondance between ideals of $A slash ker(phi)$ and
  ideals of $A$ containing $ker(phi)$. Let $pi$ be the quotient map, then $pi^*$
  is a continuous bijection $Spec(A slash ker(phi)) --> V(ker(phi))$ with
  inverse
  $
    pi' : V(ker(phi)) & -->            & Spec(A slash ker(phi)) \
                   pp & arrow.bar.long &      pi(pp). #h(4.8em)
  $
  It only remains to show that this map is continuous too. Since it is
  bijective, we only need to show that it is closed. Let $aa$ be an ideal in $A$
  containing $ker(phi)$, i.e. $V(aa)$ is a closed subspace of $V(ker(phi))$.
  Then
  $
    pi'(V(aa)) = { pi(pp) | pp in Spec(A), aa subset pp } = { pp | pp in Spec(A slash ker(phi)), aa subset pi^(-1)(pp)} = V(pi(aa))
  $
  which shows that the map is closed, thus a homeomorphism.
+ $phi^*(Y) "is dense" <==> V(0^c) = V(0) <==> V(ker(phi)) = V(0) <==> ker(phi) subset frak(N)(A)$
+ Apply the definitions
+ Note that $Spec(B) = {(0) times (1), (1)times (0)}$ (the only two other ideals
  are the zero ideal and $B$ itself, both of which are not prime) and
  $Spec(A) = {0, p}$. We have $phi^(-1)((0) times (1)) = pp$ and
  $phi^(-1)((1) times (0)) = 0$, so $phi^*$ is bijective. However, it is not
  closed since $phi^*(V((1) times (0))) = {0}$ and ${0}$ is not a closed point
  of $Spec(A)$ (it is a generic point).

#exo() $A = product_(i=1)^n A_i$, $p_i$ the projections on each $A_i$ and $pp$ a
prime ideal of $A$. Naturally, for all $i$, $p_i (pp)$ is either prime in $A_i$
or is $A_i$ itself (the primality condition is verified, but the ideal may not
be proper). Assume there is $i < j$ such that both $p_i(pp)$ and $p_j(pp)$ are
primes, which we denote by $pp_i$ and $pp_j$ respectively. Without loss of
generality, assume $i = 1, j = 2$. Then for $a in pp_1$, $b in pp_2$, we have
$(1, b, 1, dots.c) dot.c (a, 1, 1, dots.c) = (a, b, 1, dots.c) in pp$ but
$(a, 1, 1, dots.c)$ and $(1, b, 1, dots.c)$ are both not in $pp$, which
contradicts the primality of $pp$. Therefore, $pp$ is of the form
$ pp = (1) times dots.c times (1) times pp_i times (1) times dots.c times (1), $
and one verifies easily that this is indeed a prime ideal. This shows that
$Spec(A) = product.co_(i=1)^n X_i$ where
$
  X_i = A_1 times dots.c times A_(i-1) times Spec(A_i) times A_(i+1) times dots.c times A_n.
$
The $X_i$ are evidently canonically homeomorphic to $Spec(A_i)$ via $p_i$
(continuous bijective and closed).

Now let $A$ be any ring.
- i) $==>$ iii) Assume $X = Spec(A)$ is disconnected, i.e. there are two
  nonempty disjoint open subsets $U, V$ covering $X$. Mechanically, $U$ and $V$
  are also closed and of the form $V(aa)$, $V(bb)$ for some ideals $aa, bb$ of
  $A$. We have $V(aa) inter V(bb) = V(aa + bb) = emptyset$ so $aa + bb = (1)$,
  and $V(aa) union V(bb) = V(aa bb) = X$ so $r(aa bb) = frak(N)(A)$ and
  $aa bb subset frak(N)(A)$. Consider $a in aa, b in bb$ such that $a + b = 1$.
  Then $a b$ is nilpotent of cancelling order $n > 0$. We have
  $
    1 = (a+b)^(2n) = underbrace(sum_(k=1)^(n-1) binom(2n, k) a^k b^(2n-k), s_1) + binom(2n, n) underbrace(a^n b^n, =0) + underbrace(sum_(k=n+1)^(2n) binom(2n, k) a^k b^(2n-k), s_2).
  $
  We found two elements $s_1, s_2$ such that: $s_1 + s_2 = 1$ and $s_1 s_2 = 0$
  (all the terms have $a^n b^n=0$ as a factor). Therefore, they are roots to
  $X^2-X$ and at least one of them is nonzero (since $s_1+s_2=1$) and not $1$
  since it is in either $aa$ or $bb$ which are proper ideals.
- iii) $==>$ ii) Let $e$ be a nontrivial idempotent. We shall show that the
  canonical map
  $
    varphi: A & --> A slash e A times A slash (1-e) A \
            x & arrow.bar.long (x mod e A, x mod (1-e)A)
  $
  is an isomorphism. If $varphi(x)=0$ then $x = e s = (1 - e)t$ so
  $e x = e^2 s = e s = x = e(1-e)t = 0$ whence $x=0$ and $varphi$ is injective.
  Then, if $(overline(a), overline(b))$ is in the product above, then take
  $x = (1 - e) a + e b$ so that
  $varphi(x) = (overline((1-e)a), overline(e b)) = (overline(a), overline(b))$.
  Therefore, $varphi$ is an isomorphism.
- ii) $==>$ i) This was done above at the start of the exercise.

#exo()
+ For each $f$, $X_f$ is open. Let $g = 1 - f$. We have
  $V(g) inter V(f) = emptyset$ since $s + f = 1$, and
  $V(g) union V(f) = V(g f) = V(0) = X$, whence $V(g)$ and $V(f)$ are
  complements, and $X_f = V(g)$ is closed.
+ $X_(f_1) union dots.c union X_(f_n) = X without V((f_1, dots.c, f_n)) = X without V(f)$
  since every finite type ideal is principal in $A$.
+ $Y subset.eq X$ clopen, $Y = union_f X_f$, $Y$ is closed in $X$ which is
  quasi-compact, so $Y$ is quasi compact and $Y$ a finite union of $X_f$, and
  that union is again of the form $X_f$ as per the previous point.
+ We only need to show that $X$ is Hausdorff. Let $x, y in X$ be distinct
  points, wlog $pp_x subset.not pp_y$ and there is $f in pp_y without pp_x$ so
  that $V(f)$ and $X_f$ are both opens and they separate $x$ and $y$.

#skipexo()
#skipexo()

#exo() There is no problem _per se_. The book shows that if $X$ is compact
Hausdorff, then $X iso Max(C(X))$ where $C(X)$ is the ring of continuous
functions $X --> RR$.

// == Affine algebraic varieties

#exo() Once again, there is no problem _per se_. Let $k$ be algebraically closed
and let $I$ be an ideal of $k[t_1, dots.c, t_n]$. The set of points $x in k^n$
such that $f(x)=0$ for all $f in I$ is called _algebraic affine variety_, which
we denote by $X$. Let $I(X)$ be the ideal of $k[t_1, dots.c, t_n]$ consisting of
zero everywhere polynomials (the kernel of the map
$k[t_1, dots.c, t_n] --> {X --> k}$). The quotient ring
$P(X) = k[t_1, dots.c, t_n] slash I(X)$ is called the ring of polynomial
functions on $X$.

The image $xi_i$ of $t_i$ in $P(X)$ is called the $i$-th coordinate function,
and together they generate $P(X)$ as a $k$-algebra, hence why $P(X)$ is also
called the coordinate ring of $X$.

For $x in X$, the ideal $mm_x$ of all functions $f in P(X)$ such that $f(x)=0$
is a maximal ideal of $P(X)$, so that if $tilde(X) = Max(P(X))$, there is a
canonical map $mu : X --> tilde(X), x |-> mm_x$. This map is bijective! Showing
this property yields Hilbert's Nullstellensatz: there is a one-to-one
correspondance between maximal ideals of $P(X)$ and solutions to
${f(x) = 0, f in I(X)}$

#exo() Let $varphi$ be the map
$
  varphi : { X --> Y "regular" } & --> { P(Y) --> P(X) space k"-algebra morphism" } \
  phi & arrow.bar.long (eta |-> eta compose phi)
$
- _Injectivity_. Let $phi, phi'$ be regular mappings $X -->Y$ such that
  $varphi(phi)=varphi(phi')$, that is, for all $eta in P(Y)$,
  $eta compose phi = eta compose phi'$. In particular, taking $eta = xi_i$ for
  each $1 <= i <= m$ shows that $phi$ and $phi'$ share all of their coordinates
  on $X$, whence $phi = phi'$.
- _Surjectivity_. Let $f : P(Y) --> P(X)$ be a $k$-algebra morphism. Define
  $ phi = (f(xi_1), dots.c, f(xi_m)) $
  where the $xi_i$ are the coordinate functions in $P(Y)$. For each
  $1 <= i <=m$, we have
  $ xi_i compose phi = f ( xi_i), $
  which implies that for all $eta in P(Y)$, $eta compose phi = f(eta)$ (since
  $P(Y)$ is generated as a $k$-algebra by the $xi_i$, and $f$ is a $k$-algebra
  morphism) and thus $varphi(phi)=f$. The only remaining thing is to show that
  $phi$ is regular, which directly comes from the fact that each coordinate
  $phi_i$ of $phi$ is an element of $P(X)$ which is the ring of polynomial
  functions. To realise $phi$ as a restriction of a polynomial mapping, one only
  has to choose an element of $pi^(-1)(phi_i) = lambda + I(X)$ where
  $pi : k[t_1, dots.c, t_n] --> P(X)$ is the canonical quotient map and $lambda$
  is any polynomial in $pi^(-1)(phi_i)$ (nonempty by surjectivity of $pi$).

= Modules


#exo() There are $u, v$ such that $u n + v m = 1$. Let's compute simple tensors:
$
  x tens y = (u n + v m ) (x tens y) = x tens u n y + v m x tens y = x tens 0 + 0 tens y = 0.
$

#exo() We have a SES
$ 0 --> aa --> A --> A slash aa --> 0. $
The tensor product is right-exact, so we get the ES
$ aa tens_A M --> A tens_A M --> A slash a tens_A M --> 0 $
which is equivalent to
$ aa M --> M --> A slash aa tens_A M --> 0. $
We immediately get an isomorphism $M slash aa M iso A slash A tens_A M$.

#exo() $A$ a local ring, $M$ and $N$ finitely generated $A$-modules,
$M tens_A N = 0$. Let $mm$ be the maximal ideal of $A$ and $k = A slash mm$ the
residue field. By Exercise 2, we have $M_k = k tens M iso M slash mm M$ and by
Nakayama's lemma, if $M_k = 0$ then $M = 0$. We have
$
  M tens_A N = 0 ==> (M tens_A N)_k = 0 ==> M_k tens_k N_k = 0 ==> M_k = 0 " or " N_k = 0
$
since $M_k$ and $N_k$ are $k$-vector spaces.

Note that $(M tens_A N)_k = (M tens_A k) tens_A (N tens_A k) = M_k tens_A N_k$
and that $M_k tens_a N_k iso M_k tens_k N_k$ (canonically with the obvious map).

#exo() Let $M = oplus.big_(i in I) M_i$ where $M_i, i in I$ is a family of
$A$-modules. If each $M_i$ is flat, there is $M'_i$ such that $M_i oplus M'_i$
is free, and $M oplus M'$ is free with $M' = oplus.big_i M'_i$, making $M$ flat.
Assume now that $M$ is flat, and consider a SES
$ 0 --> B -->^f C --> D --> 0. $
Since $M$ is flat, we know that $f tens_A id_M: B tens_A M --> C tens_A M$ is
injective. Write
$ B tens_A M = oplus.big_i (B tens_A M_i) $
and assume there is $i in I$ such that $B tens_A M_i --> C tens_A M_i$ is not
injective, i.e. there is a nonzero tensor $t in B tens_A M_i$ such that
$(f tens_A id_(M_i))(t) = 0$. Denote by $iota_i : M_i --> M$ the inclusion map.
We get $(f tens_A id_M)((id_B tens_A iota_i)(t)) = 0$ (this is because
$id_M = oplus.big_j iota_j$ whence
$f tens_A id_M = oplus.big_j f tens_A iota_i$). Evidently,
$(id_B tens_A iota_i)(t) !=0$ which contradicts the injectivity of
$f tens_A id_M$. Thus, every map $B tens_A M_i --> C tens_A M_i$ is injective
and each $M_i$ is flat.

#exo() Write $A[x] = oplus_(n >= 0) x^n A$ and $forall n >= 0, x^n A iso A$ as
an $A$-module. Exercise 4 concludes.

#exo() $M[x]$ is an $A[x]$-module (verify each axiom). Write $A_i = x^i A$ and
$M_i = A_i tens_A M = x^i M$ so that $A[x] = oplus.big_i A_i$ and
$M = oplus.big_i M_i$. We get
$ A[x] tens_A M = oplus.big_i (A_i tens_A M) = oplus.big_i M_i = M. $

#exo() Let $pp$ be a prime ideal in $A$, and let $f(x), g(x)$ be elements of
$A[x]$ such that
$
  f(x) & = a_0 + a_1 x + dots.c + a_n x^n \
  g(x) & = b_0 + b_1 x + dots.c + b_m x^m.
$
Assume neither $f(x)$ nor $g(x)$ belongs to $pp[x]$. Let $i <= n$ be the minimal
index such that $a_i in.not pp$ and $j <= m$ be the minimal index such that
$b_j in.not pp$. The coefficient of $f(x) g(x)$ in degree $i+j$ is
$
  sum_(k=0)^(i+j) a_k b_(i+j-k) = sum_(k=0)^(i-1) underbrace(a_k, in pp) b_(i+j-k) + sum_(k=0)^(j-1) a_(i+j-k) underbrace(b_k, in pp) + a_i b_j in.not pp,
$
thus $f(x) g(x) in.not pp[x]$, and $pp[x]$ is a prime ideal in $A[x]$. Let $mm$
be a maximal ideal of $A[x]$. The ideal $mm[x] + (x)$ is a bigger proper ideal,
whence $mm[x]$ is not maximal.

#exo()
+ $B --> C$ injective, $M tens B --> M tens C$ injective,
  $M tens N tens B --> M tens N tens C$ injective.
+ Let $j : M --> M'$ be an injective morphism of $A$-modules. The map
  $j tens_A id_B$ is an injective map of $A$-modules between $B$-modules (via
  extension of scalars), and $(j tens_A id_B) tens_B id_N$ is an injective
  morphism of $B$-modules. Since
  $ (M tens_A B) tens_B N = M tens_A (B tens_B N) = M tens_A N $
  per Exercise 2.15 (in the notes), and the same goes for $M'$, we found that
  the map $j tens_A N$ is injective, thus $N$ is flat.

#exo() Consider the SES of $A$-modules
$ 0 --> M' -->^f M -->^g M'' --> 0. $
Assume $M'$ and $M''$ are finitely generated, that is, there are epimorphisms
$alpha : A^n --> M'$ and $beta : A^m --> M''$. We get the following diagram,
with exact rows and columns
#align(center, diagram({
  node((-1, -1), [$0$])
  node((0, -1), [$A^n$])
  node((1, -1), [$A^n times A^m$])
  node((2, -1), [$A^m$])
  node((3, -1), [$0$])
  node((-1, 0), [$0$])
  node((0, 0), [$M'$])
  node((1, 0), [$M$])
  node((2, 0), [$M''$])
  node((3, 0), [$0$])
  node((0, 1), [$0$])
  node((1, 1), [$0$])
  node((2, 1), [$0$])
  edge((-1, -1), (0, -1), "->")
  edge((0, -1), (1, -1), [$(id, 0)$], label-side: left, "->")
  edge((1, -1), (2, -1), [$(0, id)$], label-side: left, "->")
  edge((2, -1), (3, -1), "->")
  edge((-1, 0), (0, 0), "->")
  edge((0, 0), (1, 0), [$f$], label-side: right, "->")
  edge((1, 0), (2, 0), [$g$], label-side: right, "->")
  edge((2, 0), (3, 0), "->")
  edge((2, -1), (2, 0), [$beta$], label-side: left, "->")
  edge((0, -1), (0, 0), [$alpha$], label-side: right, "->")
  edge((1, -1), (1, 0), [$exists?gamma$], label-side: right, "-->")
  edge((0, 0), (0, 1), "->")
  edge((1, 0), (1, 1), "->")
  edge((2, 0), (2, 1), "->")
}))
To build $gamma$, we'll define it on $A^n$ and on $A^m$. Choose
$gamma|_(A^n) = f compose alpha$. Choose $y_i$ an element of $g^(-1)(beta(e_i))$
for each $1 <= i <= m$, where $(e_i)_i$ is the canonical basis of $A^m$. Then,
set $gamma|_(A^m) : e_i |-> y_i$.

It only remains to show that this map is indeed surjective. Write
$M = union.big_(y in M'') g^(-1)({y})$ and if $x in g^(-1)({y})$ then
$g^(-1)({y}) = x + ker(g) = x + im(f) = x + im(gamma|_(A^n))$ and for all
$x' in g^(-1)({y})$ we have $x'-x in im(gamma|_(A^n))$ so there is $a in A^n$
such that $x'-x = gamma|_(A^n)(a)$ and there is $b in A^m$ such that
$beta(b)=g(x)$ so that $x = gamma|_(A^m)(b)$. Finally, we get
$gamma(a, b) = gamma(a, 0) + gamma(0, b) = x'-x + x = x'$. Done!

#exo() Let $A$ be a ring and $aa subset frak(R)$ an ideal; $M$ an $A$-module and
$N$ a finitely generated $A$-module. Let $u : M --> N$ be a morphism such that
the induced map $M slash aa M --> N slash aa N$ is surjective.

The map $M --> N slash aa N$ sends $m$ to $overline(u(m)) in N slash aa N$ and
is surjective (composition of surjective maps), thus
$overline(u(M)) = N slash aa N$ and $u(M) + aa N = N$. By Nakayama's lemma
(Corollary 2.7) we have $u(M) = N$, hence the surjectivity of $u$.

#exo() Let $A$ be a nontrivial ring and let $m,n$ be integers such that
$A^m iso^phi A^n$. Let $mm$ be a maximal ideal of $A$. Then
$id_(A slash mm) tens_A phi$ is an isomorphism between $A slash mm$-vector
spaces, and equality of dimension yields $m=n$. To see that this map is indeed
an isomorphism, apply the right-exact tensor to the ES
$ 0 --> A^m -->^phi A^n --> 0. $

- Suppose now that $phi : A^m --> A^n$ is only surjective. Using the SES
  $ 0 --> A^m slash ker(phi) --> A^m --> A^n --> 0, $
  and using the right-exactness of $(A slash mm) tens_A -$, we get surjectivity
  of the $k$-vector space morphism $id_k tens_A phi$ where $k = A slash mm$.
- Now assume that the map $phi : A^m --> A^n$ is only injective. If $m > n$ the
  morphism $phi$ can be seen as an injective endomorphism
  $phi : A^m --> A^m = A^n oplus A^(m-n)$. Since $A^m$ is finitely generated, we
  have a relationship
  $ phi^r + a_1 phi^(r-1) + dots.c + a_r = 0 $
  for some $r > 0$. Since $phi$ is injective, it is left-regular, thus if $r$ is
  taken to be minimal we may assume $a_r != 0$ (otherwise LHS is of the form
  $phi compose P(phi) = phi compose 0 ==> P(phi)=0$ with $deg P < r$,
  contradiction). We have $im(phi) = A^n subset.neq A^n oplus A^(m-n)$ and thus
  $forall k > 0, im(phi^k) subset A^n$. Take
  $x = (0, dots.c, 0, 1) in A^n oplus A^(m-n)$, $x != 0$. We have
  $ phi^r (x) + dots.c + a_(r-1) phi(x) + a_r x = 0 $
  and projecting this relation the last coordinate of $A^m$ yields $a_r = 0$,
  contradiciton. Thus, $m <= n$.

#exo() Let $M$ be a finitely generated $A$-module and $phi : M --> A^n$ be a
surjective morphism. Let $e_1, dots.c, e_n$ be the canonical basis of $A^n$ and
choose $u_i in phi^(-1)(e_i)$ for each $1 <= i <= n$.

Define $psi : A^n --> M$ by $e_i |-> u_i$. Set $m in M$. We have
$ phi(m) = a_1 e_1 + dots.c + a_n e_n $
so $psi(phi(m)) = a_1 u_1 + dots.c + a_n u_n$. Clearly, since
$phi compose psi = id_(A^n)$, then $m - psi(phi(m)) in ker(phi)$. The
decomposition $m = (m - psi(phi(m))) + psi(phi(m))$ shows that
$M = N plus ker(phi)$ where $N$ is the submodule generated by
$u_1, dots.c, u_n$.

To show that the sum is direct, we merely need to show $ker(phi) inter N = 0$,
which is true since $m in ker(phi) inter N$ implies
$m = a'_1 u_1 + dots.c + a'_n u_n$ and
$phi(m) = 0 = a'_1 e_1 + dots.c + a'_n e_n$ thus $a'_i =0$ for all $1 <= i <= n$
since $e_1, dots.c, e_n$ is a basis, and $m = 0$.

To conclude, note that since $M$ is finitely generated, there is a surjective
morphism $A^m --> M = N oplus ker(phi)$ thus there is also a surjective mohpsism
$A^m --> ker(phi) = M slash N$ which shows $ker(phi)$ is finitely generated.

#exo() Let $f : A --> B$ be a ring homomorphism and let $N$ be a $B$-module seen
as an $A$-module through restriction of scalars. Let $N_B = B tens_A N$, which
is a $B$-module. Let $g : N --> N_B$ be the morphism $y |-> 1 tens y$.

Define $p : N_B --> N$ by $b tens y |-> b y$ so that $p compose g=id_N$. This
implies $g$ is injective. Then, write for $y in N_B$,
$y = (y - g(p(y))) + g(p(y))$, so that the first term $y - g(p(y)) in ker(p)$.
Thus, we have $N_B = im(g) + ker(p)$. To see that this sum is direct, take
$y in ker(p) inter im(g)$ so that $y = g(x)$ and $p(y) = p(g(x)) = x = 0$ thus
$y=0$ and $ker(p) inter im(g)=0$.

// == Direct limits

#exo() Nothing to do here. Let's break down the construction.
$MM = (M_i, mu_(i j))$ a direct system over the directed set $I$. Let
$ C = oplus.big_(i in I) M_i $
and $D$ be the submodule generated by the $x-mu_(i j)(x)$ when $i <= j$. Taking
the quotient $C slash D$ essentially comes down to taking the direct sum of the
$M_i$ but modulo the extra relation $x = mu_(i j)(x)$ whenever $x in M_i$. Note
that when $x in M_i$, $mu_(i j) (x)$ is an element of $M_j$ (where $j >= i$). We
are therefore glueing $M_i$ and $M_j$ together along $mu_(i j)(M_i)$ with the
map $mu_(i j)$. We define $M = C slash D$ and we let $mu : C --> M$ be the
canonical quotient map, with restrictions $mu_i : M_i --> M$.

Let's have a quick example. Let $I = NN without {0}$ be the direct set ordered
by divisibility ($n <= m <==> n divides m$, the LCM makes this a directed set).
Let us consider the direct limit $M = injlim_(n>0) frac(1, n) ZZ$. The maps for
the direct system are the inclusions $frac(1, n) ZZ arrow.r.hook frac(1, m) ZZ$
for $n | m$.

An element $m$ of $M$ is the class of an element in the direct sum of all the
$frac(1, n) ZZ$, meaning it is the class of a fraction of the form
$
  x = sum_(i=1)^r a_i/i = 1/(lcm(1, ..., r)) sum_(i=1)^r a_i underbrace(lcm(1, ..., r)/i, in ZZ)
$
for some $r>0$, whence $x in frac(1, lcm(1, ..., r)) ZZ$. In fact,
$ injlim_(n > 0) frac(1, n) ZZ = union.big_(n > 0) frac(1, n) ZZ = QQ. $

#exo()
- Let $x$ be an element of $M$, and choose $y in mu^(-1)(x)$. Since $y$ lives in
  the direct sum $oplus.big_(i in I)M_i$ it can be written
  $ y = sum_(j in J) m_j $
  for some finite subset $J subset I$ and $m_j in M_j$. Since $I$ is direct, $J$
  has a maximal element $i_J$ in $I$ (quick induction), from which we get
  $
    x= mu(y) = sum_(j in J) mu_j (m_j) = sum_(j in J) mu_(i_J) compose mu_(j i_J) (m_j) = mu_(i_J) (sum_(j in J) mu_(j i_J) (m_j)).
  $
- Now choose $i in I$ and $x_i in M_i$ such that $mu_i (x_i) = 0$. Then $x_i$ is
  in the class of $0 in M_j$ for all $j >= i$, meaning there is one $j >= i$
  such that $0 - mu_(i j)(x_i) = 0$ whence the result.

#exo() Let us first show that $M = injlim_(i in I)M_i$ does verify the property.
Let $N$ be an $A$-module and $alpha_i : M_i --> N$ be a collection of
$A$-modules morphisms such that $alpha_i = alpha_j compose mu_(i j)$ whenever
$i <= j$. Then naturally there exists a morphism
$tilde(alpha) : oplus.big_(i in I)M_i --> N$ which is the direct sum of all the
$alpha_i$. Consider $i <= j$ and $x in M_i$. Then
$alpha(x - mu_(i j)(x)) = alpha_i (x) - alpha_j (mu_(i j)(x)) = alpha_i (x) - alpha_i (x)$.
Therefore, the glueing submodule (which we referred to as $D$ in previous
exercises) is in the kernel of $tilde(alpha)$, which therefore induces a map
$alpha : M --> N$. The identity $alpha_i = alpha compose mu_i$ is immediate
(remember: $alpha$ is a factor of the direct sum of the $alpha_i$, and the other
factor is $oplus.big_i M_i --> M$ which is the same factor as for $mu_i$). For
uniqueness, note that we can take the direct sum on the source in the previous
relationship to obtain $(oplus.big_i alpha_i) = alpha compose mu$ and $mu$ is a
surjection, therefore it is right-invertible which leaves $alpha$ to be uniquely
defined.

To show universality we now take $(M', mu'_i)$ to be a module satisfying the
property. We shall show $M iso M'$. Pick $N = M$ and
$alpha_i = mu_i : M_i --> M$. We have $alpha_i = alpha_j compose mu_(i j)$
whenever $i <= j$ so we can apply the property, which yields a morphism
$alpha : M' --> M$ such that $alpha_i = alpha compose mu'_i$. In other words,
$mu_i = alpha compose mu'_i$, for all $i in I$. Since every $x in M$ can be
written $x = mu_i (x_i)$ (Exercise 15), then it can also be written
$x = alpha(mu'_i (x_i))$ meaning $alpha$ is surjective.

To conclude, we need injectivity of the morphism $alpha$ we constructed. Note
that the (yet-to-be) universal property claims unicity of such a morphism. This
implies that $oplus.big_i mu'_i$ is surjective, as otherwise one could pick
$x in M' without (sum_i im(mu_i))$ and define another morphism
$alpha' : M' --> M$ satisfying the same relation but with
$alpha'(x) != alpha(x)$. Therefore, every $x in M'$ can be written as a (finite)
sum of $mu'_j (x_j)$ which, as we have seen in Exercise 15, with the relation
$mu'_i = mu'_j compose mu'_(i j)$ for $j >= i$, implies $x = mu'_i (x_i)$ for
some $i in I$. Thus, if $x' in ker(alpha)$, then write $x' = mu'_i (x_i)$ so
that $alpha(x') = 0 = alpha(mu'_i (x_i)) = alpha_i (x_i) = mu_i (x_i)$. Then for
some $j >= i$, we have $mu_(i j)(x_i) = 0$ (Exercise 15) and
$mu'_i (x_i) = mu'_j compose mu_(i j) (x_i) = 0$, thus $x' = 0$ and the map
$alpha$ is an isomorphism.

#exo() $I$ is a directed set and $(M_i, mu_(i j))$ is a direct system over $I$.
First, note that
$ sum M_i = union.big M_i $
in virtue of the fact that $I$ is a directed system (if $x in sum M_i$ then
$x = sum_(j in J) x_j$ for some finite subset $J$ which has a maximal element
$i_J$ in $I$ thus $x in M_(i_J)$). It only remains to show that this union is
the direct limit.

Let $alpha_i : M_i --> N$ be a collection of morphisms such that
$alpha_i = alpha_j compose mu_(i j)$ whenever $i <= j$. Since the $mu_(i j)$ are
inclusion maps, we get $alpha_i = alpha_j|_(M_i)$ whenever $M_i subset.eq M_j$.
As such, we can define $alpha : injlim M_i --> N$ as $x |-> alpha_i (x_i)$
whenever $x = mu_i (x_i)$ (which is always the case for some $i in I$). This
definition makes sense because if $x = mu_i (x_i) = mu_j (x_j)$, then there is
$k$ such that $i, j <= k$ and in $M_k$ (which contains both $x_i$ and $x_j$), we
have $mu_k (x_i - x_j) = 0$ thus there is $k' >= k$ such that
$mu_(k k') ( x_i - x_j) = 0 = x_i - x_j in M_(k')$, meaning $x_i = x_j$ (in the
"big" containing module) and
$alpha_i (x_i) = alpha_j (mu_(i j)(x_i)) = alpha_j ( x_i) = alpha_j (x_j)$.
Moreover, surjectivity of $oplus.big_i mu_i : oplus.big_i M_i --> injlim M_i$
once again proves that such a morphism with the relations
$alpha_i = alpha compose mu_i$ is unique.

Therefore, the union $union.big M_i$ satisfies the universal property of
$injlim M_i$. For actual equality, notice that the isomorphism that arises from
satisfying the universal property is the identity.

#exo() Consider the maps $nu_i compose phi_i : M_i --> N$. They satisfy the
hypothesis for the universal property, therefore they yield
$phi = injlim phi_i : M --> N$ as requested.

$
  nu_i compose phi_i = nu_j compose nu_(i j) compose phi_i = nu_j compose phi_j compose mu_(i j)
$

#exo() #[
  #let muM = $mu^((M))$
  #let muN = $mu^((N))$
  #let muP = $mu^((P))$
  Let $MM -->^f NN -->^g PP$ be an ES of direct systems. We have
  $f compose muM_i = muN_i compose f_i$ and
  $g compose muN_i = muP_i compose g_i$ thus for all $i in I$,
  $
    g compose f compose muM_i = g compose muN_i compose f_i = muP_i compose g_i compose f_i = muP_i compose 0 = 0,
  $
  which shows that $M --> N --> P$ is a sequence (i.e. $im f subset ker g$). Now
  let $x$ be an element of $ker(g) subset N$. Then $x$ can be written
  $muN_i (x_i)$ for some $i in I$, $x_i in N_i$. We have
  $ g compose muN_i (x_i) = muP_i compose g_i (x_i) = 0 $
  thus there is $j >= i$ such that $muP_(i j) compose g_i (x_i) = 0$, i.e.
  $g_j compose muN_(i j) (x_i) = 0$, whence $muN_(i j) (x_i) in ker(g_j)$. This
  means that $x$ can be written
  $ muN_i (x_i) = muN_j compose muN_(i j)(x_i) = muN_j (x_j) $
  for $x_j = muN_(i j) (x_i) in ker(g_j)$. However, we know
  $ker(g_j) = im(f_j)$, so $x_j = f_j (y_j)$ for some #box($y_j in M_i$). We
  conclude with
  $ x = muN_j (x_j) = muN_j compose f_j (y_j) = f compose muM_j (y_j) = f(y) $
  for $y = muM_j (y_j)$, which shows that $x in im(f)$ and therefore
  $ker(g) subset im(f)$, which proves exactness of the sequence
  $ M --> N --> P. $
]

// == Tensor products commute with direct limits

#exo() #[
  #let muP = $mu^((P))$
  Let $P = injlim (M_i tens N)$ be the direct limit of
  $(M_i tens N, mu_(i j) tens 1)$ and denote by $muP_i : M_i tens N --> P$ the
  maps associated to the direct limit.
  - Let $g_i : M_i times N --> M_i tens N$ be the canonical mapping associated
    to the tensor product $M_i tens N$. Passing to the limit, we get a mapping
    $g : injlim (M_i times N) --> P$. Canonically,
    $injlim (M_i times N) = M times N$ (via the maps
    $(mu_i, id_N) : M_i times N --> M times N$), so we get a map
    $g : M times N --> P$.
  - Let's show that $g$ is bilinear. Let $(m, n), (m', n) in M times N$ be two
    elements and $lambda in A$ be a scalar. There is $i in I$ such that
    $m = mu_i (m_i)$ for some $m_i in M_i$ and $m' = mu_i (m'_i)$ for some
    $m'_i in M_i$ (we can take the same $i$ for both because $I$ is directed).
    We have
    $
      g((m+m', n))=g( (mu_i, id_N) (m_i + m'_i, n)) = muP_i compose g_i ((m+m', n))
    $
    and both $muP_i$ and $g_i$ are linear, whence we get linearity in the first
    coordinate. The same steps show linearity for the second coordinate.
  - By the universal property of the tensor product, $g$ induces
    $phi : M tens N --> P$ such that #box($phi (m tens n) = g(m, n)$) for all
    $(m, n) in M times N$.
  - Let's compute $phi compose psi$. Choose $p in P$, we have $p = muP_i (x_i)$
    for some $i in I$ and $x_i in M_i tens P$. Thus,
    $
      phi compose psi (p) = phi compose psi compose muP_i (x_i) = phi compose (mu_i tens 1) (x_i).
    $
    Since $x_i$ is a finite sum of simple tensors and the relationship above is
    linear, proving that $phi compose psi (p) = p$ when $p$ comes from a simple
    tensor is enough. As such, we assume $x_i = m_i tens n in M_i tens N$ (with
    $m_i in M, n in N$). We get
    $
      phi compose psi(p) = phi ( mu_i (m_i) tens n) = g(mu_i (m_i), n) = muP_i compose g_i (m_i, n) = muP_i ( m_i tens n) = p.
    $
    We conclude $phi compose psi = id_P$.
  - The same trick shows $psi compose phi = id_(M tens N)$.

  This shows
  $ injlim (M_i tens N) iso (injlim M_i) tens N. $
]

#exo() The maps $A_i times A_i --> A, (a, a') |-> alpha_i (a a')$ induce a
bilinear map $injlim (A_i times A_i) --> A$, and canonically
$injlim(A_i times A_i) = A times A$. We get a product on $A$, we can easily
check that it make $A$ a ring. It also makes $alpha_i : A_i --> A$ into ring
homomorphisms (verify directly with $a_i, a'_i in A_i$ and the relation
satisfied by the product map above that comes from passing to the limit).

If $A = 0$, then for any $i in I$ we have $alpha_i (1) = 0$ whence
$alpha_(i j) (1) = 0$ for some $j >= i$, and since $alpha_(i j)$ is a ring
homomorphism, $A_j = 0$ (since $1=0$ in $A_j$).

#exo() #[
  #let muN = $mu^((frak(N)))$
  #let muA = $mu^((A))$
  Note first that $alpha_(i j) (frak(N)_i) subset frak(N)_j$, whence indeed
  $injlim frak(N)_i$ is well defined and
  $frak(N)=injlim frak(N)_i subset injlim A_i=A$. If $x in frak(N)_i$ then
  $x^n = 0$ for some $n>0$ and $muN_i (x^n) = muN_i (x)^n = 0$ so all elements
  of $frak(N)$ are indeed nilpotent in $A$. Now let $a$ be nilpotent in $A$. It
  can be written $a = muA_i (x_i)$ for some $x_i in A_i$. There is $n>0$ such
  that $a^n = 0$ thus $muA_i (x_i^n) = 0$ and there is $j >= i$ such that
  $mu_(i j) (x_i) in frak(N)_j$ whence the nilradical of $A$ is contained in
  $injlim frak(N)_i$.

  If $A = injlim A_i$ is not integral, i.e. there are nonzero $a, b$ such that
  $a b = 0$, then there is $i in I$ such that
  $a = alpha_i ( a_i), b = alpha_i (b_i)$ and $a_i b_i = 0$, and $a_i, b_i$ are
  both nonzero since $a, b$ are nonzero.
]

#exo() The canonical maps are
$tens.big_(j in J) b_j |-> tens.big_(j in J) b_j tens tens.big_(j in J' without J) 1$
(pick an ordering of $J'$ to make sense of the notation).

// == Flatness and Tor

= Rings and Modules of Fractions

#exo() Let $m_1, dots.c, m_n$ be generators of $M$ as an $A$-module, $S$ a
multiplicatively closed subset of $A$.
- If $s M = 0$ for some $s in S$ then obviously all fractions $m slash s = 0$
  are zero.
- If $S^(-1) M = 0$ then in particular there exist $s_1, dots.c, s_n in S$ such
  that $s_i m_i = 0$ for all $1 <= i <= n$. Denote by $s$ the product
  $s_1 dots.c s_n$ so that for all $i$, we have $s m_i = 0$ which in turn
  implies $s M = 0$.

#exo() Let $a slash s$ be an element of $S^(-1) aa$, and $x slash s'$ be an
element of $S^(-1) A$. Then
$ 1 - (a slash s) (x slash s') = (s s' - a x) slash (s s') $
and $s s' - a x in S$ since $s s' in 1 + aa$, thus $s s' - a x$ is a unit in
$S^(-1)A$. This shows $1 - (a slash s) (x slash s')$ is a unit for all
$x slash s'$, whence $a slash s$ is in the Jacobson radical of $S^(-1)A$.

Assume now that $M$ is finitely generated and $M = aa M$ for some ideal $aa$ of
$A$. Then $S^(-1) M = (S^(-1) aa)(S^(-1) M)$ with $S^(-1) aa$ is a subset of the
Jacobson radical. By Nakayama's lemma, $S^(-1) M = 0$. By Exercise 1, there is
$s in S$ such that $s M = 0$, and we have $s equiv 1 (mod aa)$.

#exo() The composite $phi: A --> S^(-1) A --> U^(-1) (S^(-1) A)$ is such that:
- It sends every element of $S T$ to a unit
- If $phi(a) = 0$ then $u a=0$ in $S^(-1) A$ for some $u in U$, i.e.
  $(t a) slash 1 = 0$ for some $t in T$ and $s t a = 0$ in $A$ for some
  $s in S$, whence $r a = 0$ for some $r in S T$.
- Elements of $U^(-1) (S^(-1) A)$ are of the form $x slash u$ for $u in U$,
  write $u = t slash 1$ for some $t in T$ and $x = a slash s$ for some $s in S$
  to get $x slash u = phi(a) phi(s t)^(-1)$.
Corollary 3.2 shows that $phi$ induces an isomorphism
$ (S T)^(-1) A iso U^(-1) (S^(-1) A). $

#exo() $S^(-1) B --> T^(-1) B, x slash s |-> x slash f(s)$ is a well defined, a
morphism, injective, surjective.

#exo()
- Denote by $frak(N)$ the nilradical of $A$. For each prime ideal $pp$, the
  nilradical of $A_pp$ is $frak(N)_pp$ (3.14) which is zero. By (3.8),
  $frak(N)=0$.
- $A = QQ times QQ$. The prime ideals of $A$ are $pp=0 times QQ$ and
  $qq=QQ times 0$. Note that as $A$-modules, $A = pp oplus qq$. Let
  $S = A without pp = QQ^times times QQ$. We have
  $A_pp = S^(-1) A = (S^(-1) pp) oplus (S^(-1) qq)$. Let's compute these two
  modules. We have $S^(-1) qq = (QQ^times)^(-1) QQ = QQ$ and
  $S^(-1) pp = QQ^(-1) QQ = 0$. Thus, $A_pp iso QQ$. Similarly, $A_qq iso QQ$.
  This shows that being integral is not a local property (since $A_pp$ is
  integral for each $pp in Spec(A)$ but $A$ is not integral).

#exo() Apply Zorn's lemma to show that $Sigma$ has maximal elements (use the
union as a maximal element for chains).

Let $S$ be in $Sigma$, $x, y in.not A without S$, then $x y in S$ therefore
$x y in.not A without S$, whence $A without S$ is prime _if it is an ideal_.
Assume now that $S$ is maximal, i.e. for all $x in.not S$, we have
$0 in {s x^n, s in S, n in NN}$, i.e. $s x^n = 0$ for some $s in S, n > 0$ and
conversely if $s x^n = 0$ for some $s in S, n>0$ then $x in.not S$. Now take
$a, b in A without S$. We have $s a^r = t b^s = 0$ for some
$s, t in S, r, s > 0$. We have $s t (a+b)^(r+s) = 0$ thus $a+b in A without S$.
Similarly, if $x in A, y in A without S$, we have $s y^n = 0$ for some $s, n$,
thus $s (x y)^n = 0$ and $x y in A without S$. If $pp subset A without S$ is
another prime ideal, then clearly $A without pp$ is a superset of $S$ that
belongs to $Sigma$, whence $A without pp = S$ i.e. $pp = A without S$, and
$A without S$ is minimal.

One checks easily that any prime ideal $pp$ yields an element $A without pp$ of
$Sigma$ and since this correspondance is inclusion reversing, minimal primes are
sent to maximal multiplicatively closed subsets (without $0$).

#exo()
+ If $A - S$ is a union of prime ideals $A without S = union.big_i pp_i$ then
  $S = inter.big_i (A without pp_i)$. It is a multiplicatively closed subset
  (check). Now take $x, y in A$ such that $x y in S$. Then
  $ forall i in I, quad x y in A without pp_i. $
  In particular, for all $i$, we have $x y in.not pp_i$ i.e. $x in.not pp_i$ and
  $y in.not pp_i$, whence $x in S$ and $y in S$.

  Conversely, assume $S$ is saturated. Notice that the only saturated set
  containing $0$ is $A$ ($0 a = 0 in S => a in S, forall a in A$). We shall show
  that $A without S$ is the union of the primes $pp in Spec(A)$ that do not meet
  $S$. It's obvious that for any such prime $pp$, $pp subset A without S$ and
  therefore
  $ union.big_(pp inter S = emptyset) pp subset A without S. $
  Suppose now that $x in A without S$. Then the ideal $(x)$ does not meet $S$
  since it is saturated ($x y in S => x in S$ which is absurd). It is therefore
  contained in an ideal, maximal for inclusion among the ideals that don't meet
  $S$. Let $aa$ be that ideal. We claim that $aa$ is prime, and this shall
  conclude the proof. Assume $x, y in.not aa$. Maximality of $aa$ ensures that
  there exist $s in S inter ((x) + aa)$ and $t in S inter ((y) + aa)$, whence
  $s t in (x y) + aa$ and $x y in.not aa$.
+ Let $S = 1 + aa$. Let $x in A$ be such that there exists $y in A$ such that
  $1 - x y in aa$. Then $x y in S$ thus $x in overline(S)$. This shows that
  $ pi^(-1)((A slash a)^times ) subset overline(S), $
  where $pi$ is the canonical map $A --> A slash aa$. Now take
  $x in.not pi^(-1)((A slash aa)^times)$, i.e. $x space (mod aa)$ is not a unit,
  let $mm$ be a maximal ideal containing $aa + (x)$ (this latter ideal is proper
  since $x$ is not a unit in $A slash aa$). For all $s in S$, $pi(s) = 1$ whence
  $s in.not mm$. Therefore, $mm inter S = emptyset$, which implies
  $x in.not overline(S)$. Theferore,
  $ overline(S) = pi^(-1)((A slash aa)^times). $

#exo()
- i) $==>$ ii)
  $(t slash 1)phi^(-1)(1 slash t)= phi^(-1)(t slash t) = phi^(-1)(1)=1$
- ii) $==>$ iii) In $S^(-1)A$, $(t slash 1) (x slash s) = 1$ implies
  $(x s') t = s s' in S$ for some $s' in S$.
- iii) $==>$ iv) $x t in S subset overline(S) ==> t in overline(S)$.
- iv) $==>$ v)
  $pp inter S = emptyset ==> pp subset A without overline(S)subset A without T ==> pp inter T = emptyset$
- v) $==>$ iii) Choose $t in T$ and suppose $t slash 1$ is not a unit in
  $S^(-1) A$. It is contained in a maximal ideal $mm' subset S^(-1)A$, which
  comes from a prime ideal $pp in Spec(A)$, with $mm inter S = emptyset$, but
  $t in mm$ so $mm inter T != emptyset$, contradiction.
- iii) $==>$ i) Let $a slash s$ be such that $phi(x slash s) = 0$. Then there is
  $t in T$ such that $t x = 0$ in $A$, and since $t in S$, we have
  $x slash s = 0$ in $S^(-1)A$, whence $phi$ is injective.

  We shall now show that it is surjective. Choose $a slash t$ in $T^(-1)A$ for
  some $a in A, t in T$. Since $t slash 1$ is a unit in $S^(-1)A$, write
  $(t slash 1)^(-1) = b slash s$ with $b in A, s in S$. Since
  $
    a slash t = (a slash 1)(t slash 1)^(-1) = (a slash 1)(b slash s) = (a b) slash s,
  $
  we have $phi((a b) slash s) = a slash t$, whence $phi$ is surjective.

#exo() Let $pp$ be a minimal prime ideal, then (Exercise 6) $S = A without pp$
is maximal among the multiplicatively closed subsets of $A$ not containing $0$.
$S_0 S$ is a multiplicatively closed subset that does not contain $0$ and that
contains $S$, thus $S = S_0 S$ and $S_0 subset S_0 S = S$ which shows that
$pp subset D$.
+ Let $S$ ba a multiplicatively closed subset of $A$ containing a zero divisor
  $x in S$. Let $y in S$ be such that $x y= 0$ and $y != 0$ (it exists since $x$
  is a zero divisor). Automatically, $y slash 1 = 0$ in $S^(-1) A$ (since
  $s y = 0$ for $s = x in S$), thus $A --> S^(-1)A$ is not injective.
+ Let $a slash s$ be an element of $S_0^(-1) A$. Then either $a in D$ in which
  case there is a nonzero $b$ such that $a b = 0$, and $b slash 1 != 0$ (since
  elements of $S_0$ are non-zero-divisors) whence $(a slash s) (b slash 1) = 0,$
  or $a in S_0$ and $a slash s$ is automatically a unit.
+ Use Exercise 8 with $S = {1}$ and $T = S_0$, and notice that in this case
  $t slash 1$ is a unit in $S^(-1)A = A$ for each $t in S_0 = A^times$. Use iii)
  $==>$ i) to conclude.

#exo()
+ Let $I' subset S^(-1)A$ be a finitely generated ideal. It is the extended
  ideal (3.11) of a finitely generated ideal (write out the generators of $I'$
  and extract a family in $A$) thus there is an ideal $I subset A$ such that
  $I' = S^(-1) I$. Since $A$ is absolutely flat, there is an ideal $J$ such that
  $I oplus J = A$ thus
  $
    S^(-1)A = S^(-1) (I oplus J) = S^(-1) I oplus S^(-1) J = I' oplus S^(-1) J,
  $
  thus $I$ is a direct summand of $S^(-1)A$, which makes it an absolutely flat
  ring.
+ $(==>)$ The rings $A_mm$ are local and absolutely flat (as localisations of an
  absolutely flat ring) therefore they are fields (Exercise 2.28). \
  $(<==)$ $M$ an $A$-module. For each maximal $mm$, $M_mm$ is a free
  $A_mm$-module (vector space), thus it is flat. Since flatness is local, $M$ is
  local.

#exo()
- i) $==>$ ii) Assume $A slash frak(N)$ is absolutely flat. Note that
  $Spec(A slash frak(N)) iso Spec(A)$ as topological spaces with a canonical
  isomorphism coming from the canonical quotient map #box(
    $pi : A --> A slash frak(N)$,
  ). Suppose $pp in Spec(A)$ is contained in a maximal ideal $mm in Spec(A)$,
  these ideals correspond to ideals
  $overline(pp) subset overline(mm) subset A slash frak(N)$ with $overline(mm)$
  maximal as well. This implies $overline(pp)_(overline(mm))$ and
  $overline(mm)_(overline(mm))$ are also ideals, respectively prime and maximal,
  of $(A slash frak(N))_overline(mm)$ (3.13). By Exercise 10,
  $(A slash frak(N))_overline(mm)$ is a field, whence
  $(0) = overline(mm)_overline(mm)=overline(pp)_overline(mm)$. This implies that
  $overline(pp)=overline(mm)$ since the correspondance is one-to-one, and this
  in turn implies $pp = mm$ from the homeomorphism above. Thus, all prime ideals
  are maximal.
- ii) $==>$ i) All prime ideals of $A slash frak(N)$ are maximal (via the usual
  correspondance) thus for any maximal $mm in Spec(A slash frak(N))$,
  $(A slash frak(N))_mm$ is local and has a unique prime ideal, which is
  $mm_mm$. Therefore, $mm_mm$ is the nilradical of the localisation, which is
  zero since $A slash frak(N)$ has no nilpotents (and the nilradical of the
  localisation is the localisation of the nilradical). Thus,
  $(A slash frak(N))_mm$ is a field, for all maximal $mm$. Exercise 10
  concludes.
- i/ii) $==>$ iv) Let $pp_x != pp_y$ be two prime (maximal) ideals of
  $A slash frak(N)$. There are $f in pp_x, g in pp_y$ such that $f+g=1$. The
  principal opens $X_f$ and $X_g$ are neighborhoods of $y$ and $x$ respectively.
  Since $A slash frak(N)$ is absolutely flat, there are idempotents $e$, $e'$
  such that $(f) = (e)$ and $(g) = (e')$. Take $e'' = e(1-e')$, it is still
  idempotent and in $(f)$. We have $e'' in (f) subset pp_x$,
  $e' in (g) subset pp_y$, thus if $pp_z in X_f inter X_g$, then
  $e'', e' in.not pp_z$. However, $e'' e' = e(1-e')e' = 0 in pp_z$, which
  contradicts primality of $pp_z$. Thus $X_f inter X_g = emptyset$ and
  $Spec(A) iso Spec(A slash frak(N))$ is Hausdorff.
- iv) $==>$ iii) Hausdorff spaces are $T_1$.
- iii) $==>$ ii) See Exercise 1.18 for details. If $pp_x in Spec(A)$ then
  $pp_x subset pp_y$ implies $y in overline({x}) = {x}$ i.e. $pp_y = pp_x$, thus
  $pp_x$ is maximal.

#exo() Clearly, $T(M)$ is a submodule of $M$.
+ Choose $overline(m) in T(M slash T(M))$ for some $m in M$ and
  $a in Ann(overline(m)) without {0}$, then $a overline(m) = 0$ thus
  $a m in T(M)$ and since $A$ is integral, $m in T(M)$ thus $m = 0$ and
  $overline(m)=0$, whence $M slash T(M)$ is torsion-free.
+ $a f(m) = f(a m) = 0$ for $m in T(M)$.
+ Point ii) shows that the sequence makes sense. $T(M') --> T(M)$ is injective
  as a restriction of $f: M' --> M$. Choose $x in ker (g: T(M) --> T(M''))$,
  then $x in ker(M --> M'') = im(M' --> M)$ i.e. $x = f(m')$ for some
  $m' in M'$, for $a in Ann(x) != 0$ we have $f(a m) = a x = 0$ and by
  injectivity, $a m = 0$ whence $m in T(M')$ which shows exactness at $T(M)$.
+ $a slash b tens m |-> a m slash b$ is an isomorphism $K tens_A M iso Frac(A)$,
  thus $1 tens m = 0$ iff $m slash 1 = 0$ in $Frac(A)$ iff
  $exists a in A without {0}$ s.t. $a m = 0$.

#exo() First, $T(S^(-1)M)$ and $S^(-1) (T M)$ are both submodules of $S^(-1) M$.
Is $0 in S$ then the result is obvious (all the modules are trivial). From now
on we assume $0 in.not S$. For $m in M, s in S$,
$
  m slash s in T(S^(-1) M) & <==> exists a != 0, a (m slash s) = 0 \
                           & <==> exists a != 0, exists t in S, t a m = 0 \
                           & <==> exists a != 0, a m = 0 \
                           & <==> m in T(M) \
                           & <==> m slash s in S^(-1)(T M)
$
Now to show the equivalence, notice that $i)$ is equivalent to injectivity of
#box($M --> Frac(A) tens_A M$), and of course ii) and iii) are equivalent to
injectivity of the corresponding localised map. Since injectivity is local, we
get the equivalence for free.

#exo() M an $A$-module and $aa$ an ideal of $A$. Then $M slash aa M$ is an
$A slash aa$-module. Maximal ideals of $A slash aa$ come from maximal ideals of
$A$ containing $aa$. For each maximal ideal $overline(mm)$ of $A slash aa$
coming from $mm in Spec(A)$ (maximal containing $aa$), we have
$ (M slash aa M)_overline(mm) = (M slash aa M)_mm = M_mm slash (aa MM)_mm = 0, $
whence $M slash aa M = 0$ and $M = aa M$.

#exo() The problem is essentially solved but let's go through the argument. Let
$A$ be a ring and let $F$ be the $A$-module $A^n$. Let $x_1, dots.c,  x_n$ be a
set of generators of $F$ and let $e_1, dots.c, e_n$ be the canonical basis of
$F$. The application $
  phi : F & --> F\
  e_i & |--> x_i
$
This map is well defined by linearity, and surjective since the $x_i$ generate
$F$. We want to show that this map is injective, and since injectivity is local,
we may assume $A$ to be a local ring with maximal ideal $mm$. Set $N = ker phi$
and $k = A slash mm$. Since $F$ is a free $A$-module, it is also a flat
$A$-module, therefore the SES $ 0 --> N --> F --> F --> 0$ yields the SES $
  0 --> k tens_A N --> k tens_A F -->^(1 tens phi) k tens_A F --> 0.
$
We have $k tens_A F = k^n$ which is an $n$-dimensional vector space over $k$,
and $1 tens_A phi$ is surjective, thus surjective (injectivity and surjectivity
are equivalent for vector space endomorphism in finite dimension). Thus, $k
tens_A N = 0 = N slash mm N$ so $N = mm N$. The ideal $mm$ is contained in the
Jacobson of $A$ (it is the Jacobson), thus $N = 0$ by Nakayama's lemma, and
$phi$ is an isomorphism.

Suppose now that $x_1, dots.c, x_r$ is a generating family, with $r < n$. Then
we can add any element to the family to get the generating family $x_1, dots.c,
x_n$, which is a basis. Since it is a basis, $x_n$ is not a linear combination
of $x_1, dots.c, x_(n-1)$, which shows $x_1, dots.c, x_r$ does not generate $F$,
contradiction.

#exo() Let $f$ be the (ring) map $A --> B$ making $B$ a flat $A$-algebra.
- i) $==>$ ii) $Spec(B) --> Spec(A)$ is surjective iff $forall pp in Spec(A),
  exists qq in Spec(B)$ such that $pp = f^(-1)(qq)$. By (3.16), this is verified
  iff $pp^(e c) = pp$, which is true here by i).
- ii) $==>$ iii) Let $mm$ be a maximal ideal of $A$, then there is $qq in
  Spec(B)$ such that $mm = qq^c$, i.e. $mm^e = qq^(c e) subset.eq qq$.
- iii) $==>$ iv) Let $M$ be a nonzero $A$-module, it has a nonzero submodule
  $M'=A x$ for some nonzero $x in M$, which yields an ES $
    0 --> M' --> M --> M slash M' --> 0.
  $
  Tensor it with the flat algebra $B$ to get $
    0 --> M'_B --> M_B --> M_B slash M'_B --> 0.
  $
  We have $M' iso A slash aa$ for some ideal $aa$ contained in some maximal
  ideal whose extension is not $B$, whence $M'_B iso B slash aa^e != 0.$
- iv) $==>$ v) Let $M'$ be the kernel of $M --> M_B$. Since $B$ is flat, we have
  an ES $
    0 --> M'_B --> M_B --> (M_B)_B,
  $
  and the last map is injective per Exercise 2.13, whence $M'_B = 0$.
- v) $==>$ i) Take $M = A slash aa$.

#exo() $ A -->^f B -->^g C$, let $phi : N --> M$ be an $A$-module homomorphism.
There is a commutative diagram
#align(center, diagram({
   node((-1, -1), [$N_B$])
   node((0, -1), [$M_B$])
   node((0, 0), [$M_C$])
   node((-1, 0), [$N_C$])
   edge((-1, -1), (0, -1), [$phi_B$], label-side: left, "->")
   edge((0, -1), (0, 0), "->")
   edge((-1, -1), (-1, 0), "->")
   edge((-1, 0), (0, 0), [$phi_C$], label-side: right, "hook->")
}))
The bottom map here is injective since $g compose f$ is flat. Since $g$ is
faithfully flat, the map $ N_B --> (N_B)_C = (N tens_A B) tens_B C = N tens_B C
= N_C $ is injective. By commutativity, $phi_B$ is injective.

#exo() $f : A --> B$ a flat ring morphism, $qq in Spec(B)$, and $pp = qq^c$. The
ring $B_pp$ is flat over $A_pp$ by (3.10) (flatness is local). We have $B_qq =
(B without qq)^(-1) B$, and since $f(A without pp ) subset.eq B without qq$,
we have a map $A_pp --> B_qq$. Exercise 3 yields an isomorphism $B_qq iso S^(-1)
B_pp$ with $S = {s slash 1 in B_pp, s in B without qq }$. As a localisation,
$B_qq$ is flat over $B_pp$, and we have a natural composite map $
g: A_pp --> B_pp --> S^(-1) B_pp iso B_qq.
$
Both arrows are flat, hence $B_qq$ is flat over $A_pp$. Now notice that $A_pp$
is local with maximal ideal $pp A_pp$. We have $g(pp A_pp) subset.eq qq B_qq$
whence $(pp A_pp)^e != B_pp$ and $A_pp --> B_qq$ is faithfully flat per Exercise
16 iii). Condition ii) from that same exercise shows surjectivity of the
required map.

#exo()
+ Per (3.8), $M = 0 <==> Supp(M) = 0$. #h(1fr)
+ $
  pp in V(aa) <==> aa subset.eq pp & <==> aa inter (A without pp) = emptyset \
              & <==> forall s in A without pp,forall a in aa, quad s != a \
              & <==> forall s, t in A without pp,forall a in aa, quad t(s-a) != 0 \
              & <==> forall a slash s in aa_pp, quad a slash s != 1\
              & <==> aa_pp subset.neq A_pp \
              & <==> A_pp slash a_pp = (A slash aa)_pp != 0\
              & <==> pp in Supp(A slash aa)
  $
+ 

#pagebreak()
#pagebreak()

/*
= Primary Decomposition

= Integral Dependence and Valuations

== Noether's normalization lemma

== Nullstellensatz (weak form)

== Valuation rings and valuations

= Chain Conditions

= Noetherian Rings

= Artin Rings

= Discrete Valuation Rings and Dedekind Domains

= Completions

= Dimension Theory
*/

// vim: set tw=80:
