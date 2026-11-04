Removing the logarithmic loss in the Li–Wu KdV integrator
Kaiwen Jin
yui.ui.siki@gmail.com
10 October 2026
Abstract
Li and Wu proved that their unfiltered integrator for periodic KdV converges inL2 with
error O(τγ log(1/τ))for real, mean-zero Hγ data,0 <γ≤ 1. We remove the logarithmic factor
for the same time-semidiscrete algorithm, with constants uniform on boundedHγ sets. The
main estimate concerns the exact averaged cubic remainder. Retaining both ratios of its two
oscillatory phases bounds the dual four-frequency multiplier by the reciprocal of the third largest
frequency. A dyadic four-linear estimate sums this majorant without a logarithm and includes
a mixedL2 endpoint. That endpoint controls the remainder at the numerical state without a
numerical Sobolev bound. We then prove the full global estimate using the continuous trilinear
bounds of Li and Wu, a stepwise residual calculation, low–high frequency stability, a restarted
bootstrap, and density. Finite Fourier experiments check the implemented update, the remainder,
and accumulated step defects.
1 Introduction
Low spatial regularity limits the accuracy of time discretizations for dispersive equations. For
periodic KdV, differentiation in the quadratic nonlinearity makes a directL2 perturbation estimate
insufficient. The unfiltered method of Li and Wu integrates the leading oscillatory interactions
explicitly and treats its numerical trajectory as a perturbed KdV solution. Their convergence
theorem givesCτγ log(1/τ)in L2 forHγ data with0 <γ≤ 1[ 1, Theorem 1.1]. The necessity of the
logarithm is left open in [1, Section 11]; this is the fixed-scheme question in AIM problem 518 [3].
We prove the boundCτγ for that same method, uniformly on bounded sets of real, mean-zero
Hγ data. The improvement comes from the averaging remainder, rather than a change in the update.
Its multiplier contains the covariance of two exponential phases. Each phase can be integrated
against the other, giving two ratio bounds. Keeping their minimum matters when the output
frequency is small. After duality the four frequencies sum to zero, their largest two magnitudes
are comparable, and the remaining multiplier is controlled by1/N3, whereN3 is the third largest
magnitude. The smaller dyadic scales then carry a summable geometric factor.
The resulting trilinear estimate includes exponent zero. This is a local remainder estimate: it
does not assert a uniform global rate on anL2 ball. Its role is to compare the cubic remainder at the
numerical state with the remainder at an exactHγ state using only theirL2 difference. We retain
the continuous trilinear estimates of Li and Wu and give the residual and stability argument in full.
In particular, the normal-form identity keeps both endpoints when the time interval is restarted,
and its forcing term is estimated from the actual stepwise residual. A fixed-timestep approximation
argument then removes the temporary smoothness used in the calculations.
The experiments use a fixed finite Fourier cutoff, complete polynomial intermediates, and
independently checked reference resolutions. They illustrate the remainder and error accumulation.
1

Every computed input is a smooth Fourier polynomial, so these observations do not decide a uniform
rough-data rate or the necessity of a logarithm; that conclusion is proved analytically below.
2 The scheme and the main result
Use normalized measuredx/(2π)on T = R/(2πZ); changing to unnormalizedL2 only changes
constants. Write St = e−t∂3
x, so thatˆStf(k) = eitk3ˆf(k). Let P0 be the mean,P = I−P 0, and
define D−1 = ∂−1
x with multiplier(ik)−1 for k̸ = 0and zero at zero. Set D−2 = (D−1)2. Write
ˆf(k) = (2 π)−1∫2π
0 f(x)e−ikxdx and∥f∥ 2
Hs = ∑
k∈Z⟨k⟩2s|ˆf(k)|2,⟨k⟩ = (1 + k2)1/2. Spaces are
the completions of trigonometric polynomials in these norms, with negative spaces interpreted
as distributions. Orthogonality gives the normalizedL2 identity for polynomials and hence for
their completions. For mean-zero functions ands≥ 0,∥f∥ ˙Hs≤∥f∥ Hs≤ 2s/2∥f∥ ˙Hs; Fors <0,
2s/2∥f∥ ˙Hs ≤ ∥f∥Hs ≤ ∥f∥˙Hs. Real-valued means ˆf(−k) = ˆf(k). All time suprema concern
continuous representatives; derivative norms are essential suprema. The exact solution is the unique
real mean-zeroC([0,T ];Hγ)solution obtained by smooth approximation, and satisfies the equation
distributionally. The constantsCM may change from line to line and depend onγ,T,M , but are
uniform inn,τand spectral support.
The equation is
ut +uxxx = 1
2∂x(u2), u(0) =u 0.(1)
The fixed scheme isu0 =u 0 and
un+1 =S τun +Fτ(un) +Hτ(un), τ=T/L,(2)
where
Fτ(f) = 1
6P[(SτD−1f) 2]− 1
6SτP[(D−1f) 2],
Hτ(f) = 1
3P[(SτD−1f)D−1Fτ(f)] + τ
9(SτD−1f)P 0(f 2)
− 1
54
[
Sτ−sD−1[(SsD−1f) 3]
]s=τ
s=0
− 1
27τ
[
Sτ−sD−2[(Ss−τD−2Fτ(f))(SsD−1f)]
]s=τ
s=0
.
This is the scheme of [1, Eq. (1.4)], without a spatial frequency cutoff.
Theorem 1(Logarithm-free convergence).Let T >0,0 <γ≤ 1, andR> 0. For real, mean-zero
u0∈H γ(T)with ∥u0∥Hγ≤R , there areC,τ 0> 0, depending only onT,γ,R , such that the scheme
(2)satisfies
max
0≤n≤L
∥u(nτ)−u n∥L2≤Cτ γ wheneverτ=T/L≤τ 0.
The periodic KdV bounds of Babin–Ilyin–Titi control the exact flow on the initial-data ball. The
continuous estimates of [1, Proposition 3.4 and Lemma 7.2] will be used in the stability proof. The
logarithmic convergence theorem itself is not used. For the exact twisted solutionv(t) =S−tu(t), set
M= 1 + sup
0≤t≤T
∥v(t)∥Hγ.
The source statements and the sign transformation giving a bound forM are recorded below in
Section 2.1. No convergence theorem for the numerical scheme is used as an input. Intermediate
constants may depend onM,γ,T, but never on the timestep or a Fourier support bound.
2

2.1 The exact KdV flow
The source [2, Theorems 4.2–4.3, 5.1, 6.3–6.5] treatsUt = UUx +Uxxx on the same torus, with
normalized measure and mean-zero homogeneous Sobolev norms. Theorem 4.2 bounds its Galerkin
flows on[0,T ]in ˙Hs by a constant depending only ons,T,∥U 0∥ ˙Hs and an upper bound for∥U0∥2.
Theorem 4.3 gives a distributional limiting solution with the same bound. Theorems 5.1 (s> 1/2)
and 6.3 (0< s≤ 1/2) give its uniqueness,C([0,T ]; ˙Hs)regularity and continuous dependence.
Theorem 6.4 coverss = 0, and Theorem 6.5 withθ = 0states that, for two flows whose initialL2
norms sum to at mostB, sup[0,T]∥U− ˜U∥ 2≤C (T,B )∥U0− ˜U0∥2. Together these results specify
the continuous flow and the uniform bounds needed here.
Define u(t,x ) =−U(t,−x ). Thenut =−Ut, ux =Ux, uxxx =Uxxx at( t,−x ), and consequently
ut +uxxx = uux. Fourier coefficients become ˆu(k) = −ˆU(−k), preserving every Sobolev norm,
reality and zero mean. This transforms the source equation to(1). The norm comparison above
transfers all bounds to ourHγ norm. Hence there isA(T,γ,R )<∞ such that every smooth initial
datum in the stated ball satisfiessup[0,T]∥u(t)∥Hγ≤A . The same bound holds for the limiting
solution: for each finite set of frequencies pass to the limit in its finite norm sum, then take the
supremum over finite sets. ThusM≤ 1 +A(T,γ,R )uniformly. Continuous dependence inL2 is
precisely the input used in the final density passage. No change of torus length or amplitude scaling
is needed.
3 The averaged cubic remainder
The estimate proved in this section is uniform in the Fourier support. We begin with the exact
covariance in the update.
3.1 Covariance bounds
For realα,βlet
Mτg= 1
τ
∫τ
0
g(s)ds, η τ(α,β) =M τ(e−is(α+β))−M τ(e−isα)Mτ(e−isβ).
Fork=a+b+c, put
p=a+b, α= 3abp, β= 3kcp,Φ =α+β=k 3−a 3−b 3−c 3.(3)
In the notation of [1, Eqs. (4.15),(6.1)],
\Rn
2,τ(f1,f 2,f 3)(k) =− τ
18ik
∑
a+b+c=k
a+b̸=0
e−itnΦητ(α,β) ˆf1(a)ˆf2(b)ˆf3(c), k̸= 0,(4)
with zero output atk = 0. Terms with a zero input frequency also vanish, because thenα = 0or
β= 0.
Lemma 2(Bounds for the average covariance).Ifαβ̸= 0, then
|ητ(α,β)|≤2 min{|α/β|,|β/α|},(5)
|ητ(α,β)|≤τmin{|α|,|β|}.(6)
If either phase vanishes,ητ = 0.
3

Proof. Let h(s) = e−iαs−M τ(e−iαs). Then ητ = τ−1∫τ
0 h(s)e−iβsds. The elementary bound
|h(s)|≤τ −1∫τ
0|α||s−r|dr≤τ|α|gives (6), also interchangingαandβ. Moreover,
|h(0)|+|h(τ)|≤τ|α|,
∫τ
0
⏐⏐h′(s)
⏐⏐ds=τ|α|.
Integratinge−iβs once gives|ητ|≤ 2|α/β|. Interchanging the phases proves(5). These estimates are
consistent with [1, Lemma 3.2]; the proof here records exactly which bounds will be retained.
3.2 Four frequencies and dyadic summation
For nonzeroa,b,c,d∈Z with a +b +c +d = 0, let N1≥N 2≥N 3≥N 4 be the decreasing
rearrangement of their absolute values. ThusN3 is the third largest, or second smallest, offour
frequencies, including the dual outputd=−k. The zero-sum relation impliesN1≤3N 2.
Lemma 3(Two pointwise majorants).WriteA=|ab|andB=|cd|. Then
1
|d| min{A/B,B/A}≤ 3
N3
,(7)
|a+b|
max(A,B) ≤ 6
N3
.(8)
Proof. For(7), ifd is among the two largest frequencies, usemin(A/B,B/A )≤ 1. Otherwise the
largest two are amonga,b,c. If they area,b, then
1
|d| min(A/B,B/A)≤ |c|
|ab|≤ 1
N3
.
If they area,c (the caseb,c is identical), their ratio is between1/3and3. The remaining magnitudes
are|b|,|d|, whose maximum isN 3. Thus
1
|d| min(A/B,B/A)≤3 min
{
|b|
|d|2, 1
|b|
}
≤ 3
max(|b|,|d|) .
For (8), consider the pairing(a,b )and( c,d ). If the two largest magnitudes are in the same pair,
the other pair has sum of magnitude at most2N3. Sincea+b=−(c+d),
|a+b|
max(A,B) ≤ 2N3
N1N2
≤ 2
N3
.
If the largest two belong to different pairs, the third largest is paired with one of them. Hence
max(A,B )≥N 2N3 and|a+b|≤ 2N1≤ 6N2, giving the result. Ties can be ordered arbitrarily; the
same alternatives cover them.
Lemma 4(Third-largest-frequency four-linear estimate).For nonnegativex j∈ℓ 2(Z\{0}),
∑
a+b+c+d=0
abcd̸=0
x1(a)x2(b)x3(c)x4(d)
N3(a,b,c,d) ≤C
4∏
j=1
∥xj∥ℓ2.(9)
The same conclusion holds after restricting the sum to any subset.
4

Proof. It suffices first to consider finitely supported sequences. Decompose into shells2j≤|k|< 2j+1,
j≥ 0, and writeXr,j for theℓ2 norm of therth sequence on thejth shell. Fix an ordering of the
four shell indicesj1≥j 2≥j 3≥j 4. A nonzero zero-sum interaction hasj1−j 2≤ 2. For each fixed
pair of smaller-shell frequencies, the remaining sum of the two larger-shell sequences is at most their
ℓ2 norm product by Cauchy–Schwarz, since one sequence is a translated reflection of the other. Sum
the smaller frequencies inℓ1. A shell has at most2j+1 integer elements, so another Cauchy–Schwarz
bound gives
∑
a+b+c+d=0
4∏
r=1
xr,jr≤C2 (j3+j4)/2
4∏
r=1
Xr,jr.
Since N3≥ 2j3, the weight leavesC2−(j3−j4)/2. Forq =j1−j 2∈{ 0, 1, 2}, extend the nonnegative
sum by dropping the upper restriction on the smaller shells. The contribution is at most
C
(∑
J
X1,JX2,J−q
)
∑
ℓ≥m
2−(ℓ−m)/2X3,ℓX4,m

.
The first factor is bounded by Cauchy–Schwarz. Writingr=ℓ−m, the second is at most
∑
r≥0
2−r/2∥X3∥ℓ2∥X4∥ℓ2 =∥X3∥ℓ2∥X4∥ℓ2
1−2 −1/2 .
Sum over at most 24 orderings and three offsets. For arbitrary nonnegative sequences apply the
finite bound to their restrictions to|k|≤m . The infinite positive sum is the supremum of these
finite sums, while the norms of the restrictions are bounded by the full norms. This proves the
infinite statement without exchanging conditionally convergent sums.
3.3 The mixed remainder estimate
Theorem 5(Mixed remainder bound).For0 ≤γ≤ 1, τ > 0, and arbitrary mean-zero inputs
fj∈H γ(T),
Rn
2,τ(f1,f 2,f 3)

L2≤Cτ 1+γ
3∏
j=1
∥fj∥Hγ,(10)
uniformly inn, τ, and Fourier support. The estimate remains true if an arbitrary multiplier of
modulus at most one is inserted in the sum(4). In particular it holds separately onΦ = 0and
Φ̸= 0.
Proof. Only nonzeroabck andp =a +b̸ = 0need consideration. Set d =−k. Lemma 2 and(7) give
|η|
|k|≤ 6
N3
.
For the other endpoint, observe thatAB=|abck|, and use (6) and (8):
|η|
τ|abck| ≤3|p|min(A,B)
AB = 3 |p|
max(A,B) ≤ 18
N3
.
Taking the geometric mean of these two bounds yields
|ητ(α,β)|
|k||abc| γ ≤ 61−γ18γτγ
N3(a,b,c,−k) . (11)
5

Dualize (4)against anℓ2 sequence and take absolute values. Apply Lemma 4 withx1(a) =|a|γ
⏐⏐⏐ˆf1(a)
⏐⏐⏐
and analogously forx2,x 3; x4(d)is the absolute value of the dual coefficient at−d. Their norms
are bounded by the inhomogeneous Sobolev norms and the dual norm. The factorse−itnΦ have
modulus one. This proves the theorem, including the assertion about restricted sums. Polynomial
approximation and the bound extend the operator to the claimed spaces.
Remark6.The exponent-zero assertion above is an estimate for the local cubic remainder, not a
convergence theorem atγ= 0. The global closure below usesγ >0.
Corollary 7(A numerical-state estimate).Let w∈H γ, f∈L 2,∥w∥Hγ≤M andδ =∥f−w∥ L2≤
1. For0<τ≤1, Rn
2,τ(f,f,f)

L2≤C Mτ(τγ +δ).(12)
Proof. Apply (10) with exponentγ to(w,w,w ). Expand the difference between the cubic expressions
at f and atw, and apply its exponent-zero case to every difference term. This givesCτδ (∥f∥L2 +
∥w∥L2)2. NoH γ bound on the numerical state is used.
4 Global convergence
4.1 Continuous estimates and normal forms
Fixp∗ = 23/14>3/2and, for an intervalIof length at most one, set
∥f∥X(I) =∥f∥ L∞(I;L 2) +∥∂tf∥L∞(I;H−p∗).
Define
Bt(f,g) =S −t∂x[(Stf)(Stg)],
Jt(f,g) =S −tP[(St∂−1
x f)(St∂−1
x g)],
CI(f,g,h) =
∫
I
S−tP{P[(S tf)(Stg)](St∂−1
x h)}dt.
The normal-form identity is
∫b
a
Bt(f,g)dt= 1
3[Jt(f,g)] b
a− 1
3
∫b
a
{Jt(f′,g) +J t(f,g′)}dt.(13)
For time-smooth, spatially smooth mean-zero functions, the coefficient ofJt(f,g )at k̸ = 0is∑
a+b=ke−it3kab(ia)−1(ib)−1ˆf(a)ˆg(b). Differentiating the phase gives3ik times the product coeffi-
cients, hence∂tJt(f,g ) = 3Bt(f,g ) +Jt(f′,g ) +Jt(f,g′). Integrating proves(13). Smooth functions
have absolutely convergent Fourier sums, including every derivative appearing here. Piecewise
smooth time dependence is sufficient after applying this calculation on each step. SinceD−1∂x =P,
the second identity below follows by substituting the definition ofB; it does not require commutation
through a product. AlsoJt is symmetric and
∫
I
Jt(Bt(f,g),h)dt=C I(f,g,h).(14)
The following are the published inputs from [1, Proposition 3.4]:
∥CI(f1,f 2,f 3)∥L2≤C|I|
∏
j
∥fj∥X(I) +C∥f i∥L∞H−p∗
∏
j̸=i
∥fj∥L∞L2, i= 1,2,3,(15)
∥CI(f1,f 2,f 3)∥L2≤C α|I|α∏
j
∥fj∥Hα,0≤α≤1, f j time-independent.(16)
6

All time norms in(15) are overI. The other input is the following consequence of [1, Lemma 7.2
and Eq. (2.2)]. There existsaγ∈[0,1)such that
∥fg∥L2≤C γ∥f∥Hγ∥g∥Haγ ,(17)
and, withFn(t;w) = 1
2
∫t
tnBs(w,w)ds,
sup
tn≤t≤tn+1
∥Fn(t;w)∥Haγ≤C Mτγ,sup
tn≤t≤tn+1
∥Fn(t;w)∥H 1+γ≤C M,(18)
when∥w∥Hγ≤M . One can takeaγ = 1/2−γ for0 <γ < 1/2,1 /8for γ = 1/2, andaγ = 0for
γ >1/2. For clarity, the source stage exponent isθ = (1 +γ−β )/(1 +γ−β 0), withβ0 = 2γ− 3/2
for0 <γ < 1/2, β0 =−1/2−ϵ for γ = 1/2, andβ0 =γ− 1for1 /2<γ≤ 1. Takeϵ = 1/8in the
middle case. Atβ =aγ the exponents are respectively(1/2 + 2γ)/(5/2−γ )≥γ ,11 /17> 1/2and
(1 +γ)/2≥γ . Every aγ lies in the source interval[β0, 1 +γ]. Since0 < τ≤ 1, these exponents
imply the first bound in(18). Atβ = 1 +γ the exponent is zero, giving the second. Inequality(17)
is the source [1, Eqs. (2.2)–(2.3)], with the same fixed1/8choice when γ = 1/2. SourceL2 and Hs
norms are
√
2π times ours; dividing the source inequalities absorbs only fixed factors into constants.
These estimates require no regularity beyondHγ on w. Finally the elementary one-dimensional
bounds are
∂−1
x f

H 1 +
∂−1
x f

L∞ ≲∥f∥ L2,∥B t(f,g)∥ H−p∗ ≲∥f∥ L2∥g∥L2,∥J t(f,g)∥ H 1 ≲∥f∥ L2∥g∥L2.
(19)
The second bound usesL1(T)↪→H−p∗+1(T).
4.2 Elementary product bounds
Here are direct proofs of (19) and the variants used below. Cauchy–Schwarz in Fourier gives
∥D−1f∥∞≤ (∑
k̸=0k−2)1/2∥f∥ 2, and∥D−1f∥H 1≤
√
2∥f∥ 2. ForA,B∈H 1, the product rule and
the precedingH1 to L∞ bound give∥AB∥H 1≤C∥A∥ H 1∥B∥H 1. Thus∥Jt(f,g )∥H 1≤C∥f∥ 2∥g∥2.
Writing|ˆFG (k)|≤∥F∥ 2∥G∥2 yields∥Bt(f,g )∥2
H−p∗ ≤∥f∥ 2
2∥g∥2
2
∑
k̸=0k2⟨k⟩−2p∗. The sum is fi-
nite exactly becausep∗ > 3/2. The same coefficient bound gives∥D−1P (FG )∥2≤C∥F∥ 2∥G∥2.
For a mean-zeroA,∥A∥H−p∗ ≤∥D −1A∥2. We also use the asymmetric bound∥Jt(A,B )∥2≤
C∥D−1A∥2∥B∥2: bound the second inverse derivative inL∞ and the first inL2. All constants are
uniform int, sinceSt is an isometry in every Fourier Sobolev norm. Density extends the bounded
products from polynomials.
4.3 The continuous numerical interpolation
Initially work with smooth data. All estimates below are independent of higher Sobolev norms;
Section 4.4 removes this temporary device. Setvn =S−tnun and onIn = [tn,tn+1]write f =vn,
7

w=v(t n),δ n =∥f−w∥ L2 andq n =τ γ +δn. Assumeδ n≤1. Define
Fn(t) = 1
2
∫t
tn
Bs(f,f)ds, z n(t) =f+F n(t),
Cn(t) =
∫t
tn
Bs(f,Fn(s))ds,
Qn(t) = 1
2
∫t
tn
Bs(Fn(s),Fn(s))ds,
Wn =Q n(tn+1) +Rn
2,τ(f,f,f),
V(t) =f+F n(t) +Cn(t) +Qn(t)− t−t n
τ Wn,
Yn(t) =V(t)−z n(t).
The source identity isvn+1 =f +Fn(tn+1) +Cn(tn+1)−Rn
2,τ(f,f,f )([ 1, Eqs. (4.20)–(4.23),(5.2)]);
the Qn(tn+1)terms in our definition cancel. The source notationet∂3
x is exactly ourS−t, An is
our Cn(tn+1), and sourceRn
2 is (4). Consequently the exact identity [1, Eqs. (5.2)–(5.4)] implies
V (tn) =vn and V (tn+1) =vn+1 for the specified scheme. ThusV is continuous across the grid and
agrees there with the twisted numerical trajectory.
Stages and endpoint correction
The endpoint formulaFn(t) = 1
6[Js(f,f)] t
tn gives
sup
In
∥Fn(t)∥H 1≤C M,sup
In
∥Fn(t)−F n(t;w)∥H 1≤C Mδn.
Together with (18), this yields
sup
In
∥Fn(t)∥Haγ + sup
In
∥Fn(t)∥L2≤C Mqn,∥z n∥X(In)≤C M.(20)
For the exact-data contribution, apply(17) to ∂x(StFn(t;w))and StFn(t;w); use (18). Write
A =Fn(t;w)and D =Fn(t)−A. The exact-data term obeys∥∂x[(StA)2]∥2≤ 2Cγ∥A∥H 1+γ∥A∥Haγ≤
CMτγ. The difference of squares is(StD)St(Fn +A); both second factors have boundedH1 norm
and∥D∥ H 1≤C Mδn. TheH 1 algebra estimate bounds its derivative byCMδn. Thus
sup
In
∥Bt(Fn(t),Fn(t))∥L2≤C Mqn.
Consequently Corollary 7 implies
sup
In
∥Qn(t)∥L2 +∥Wn∥L2≤C Mτqn.(21)
The interpolation defect
To boundD−1Bt(f,Fn), use its exact expressionS−tP [(Stf)(StFn)]. The product containingw is
bounded byCγ∥w∥Hγ∥Fn∥Haγ. The product containingf−w is bounded by∥f−w∥ 2∥StFn∥∞≤
CMδn using the uniformH1 bound. Therefore
sup
In
∂−1
x Bt(f,Fn(t))

L2≤C Mqn.
8

Use (21) andY′
n =B t(f,Fn) + 1
2Bt(Fn,Fn)−τ −1Wn to get
sup
In
∂−1
x Yn

L2≤C Mτqn,sup
In
∂−1
x Y′
n

L2≤C Mqn.(22)
For the strong norm, (13) andF′
n = 1
2Bt(f,f)give exactly
Cn(t) = 1
3Jt(f,Fn(t))− 1
6C[tn,t](f,f,f).
The first term isO(qn)in L2. In the second, use(16) with exponentγ on( w,w,w ), and exponent
zero on every term in the difference with(f,f,f). Thus
sup
In
∥Yn∥L2≤C Mqn.(23)
Sincep∗>1, (22)–(23) imply the important pair
∥Yn∥X(In)≤C Mqn,sup
In
∥Yn∥H−p∗≤C Mτqn.(24)
The residual
Define on a step
ρn(t) =−
∫t
tn
Bs(Yn,zn)ds− 1
2
∫t
tn
Bs(Yn,Yn)ds− t−t n
τ Wn.
Concatenate these increments intoR(t), withR(0) = 0. Then
V′ = 1
2Bt(V,V) +R ′,R ′ =−B t(Yn,zn)− 1
2Bt(Yn,Yn)−τ −1Wn.(25)
We claim
sup
In
∥ρn∥L2≤C Mτqn,
R′
L∞(In;H−p∗)≤C Mqn.(26)
For the first integral inρn, apply(13). The boundary term and the term containingY′
n are each
O(τqn)by (22) and∥zn∥L2 ≲ 1. Sincez′
n = 1
2Bt(f,f ), the remaining term is a constant multiple
ofC(f,f,Y n). In (15), put the negative norm onYn and use(24); the result is alsoO(τqn). For
the second integral apply (13) with Yn in both slots. Its boundary and derivative terms are
O(τq 2
n) =O(τqn)because qn≤ 2. TheWn term is controlled by(21). This proves the first claim.
The second follows directly from (25), (19), (21), and (23).
4.4 Stability and completion of the proof
Set e = v−V . On an interval I = [a,b ]starting at a grid point, with h = b−a≤ 1, let
EI = supI∥e∥L2 and assumeEI≤ 1. The interval may end inside a step. The preceding bounds
imply
sup
a≤t≤b
∥R(t)−R(a)∥ L2≤C M(h+τ)(τ γ +EI),(27)
∥e∥X(I)≤C M(τγ +EI),∥v∥ X(I) +∥V∥ X(I)≤C M.(28)
Indeed e′ =Bt(e,v−e/ 2)−R′. There are at mosth/τ + 1intersected steps, each starting with
δn≤E I, so (26) proves the first bound and theH−p∗ product estimate proves the second.
9

For anyt∈I, defineF I(t) =
∫t
aBs(e,v−e/2)ds. The exact error identity is
e(t) =e(a) +F I(t)−
(
R(t)−R(a)
)
.(29)
Choose a Fourier thresholdN≥ 2only in the proof. It is not part of the algorithm. The low
frequencies satisfy
sup
t∈I
∥P≤NFI(t)∥L2≤C MN 2hEI.(30)
For example
∂−1
x P(fg)

L2 ≲∥f∥ L2∥g∥L2, followed by the two-derivative Bernstein bound, proves
(30).
For high frequencies, (13) gives, retainingbothendpoints,
FI(t) = 1
3[Js(e,v−e/2)] s=t
s=a− 1
3C[a,t](e,v−e/2,V)− 1
6C[a,t](v,v,e) + 1
3
∫t
a
Js(R′,V)ds.(31)
For an explicit verification putg =v−e/ 2. Thene′ =B(e,g )−R′ andg′ = 1
2B(v,v )− 1
2B(e,g )+ 1
2R′.
In the differentiated terms of(13), symmetry ofJ givesC(e,g,g )− 1
2C(e,g,e ) =C(e,g,V )because
g−e/ 2 = V. The remaining cubic term is 1
2C(v,v,e ), and the forcing terms are−J (R′,g ) +
1
2J (e,R′) =−J (R′,V ). Multiplication by−1/3yields exactly (31). The endpoint terms afterP>N
are bounded byCMN−1EI by theH 1 bound forJin (19).
We spell out how the high-output trilinear terms are estimated. If all three inputs have frequencies
at mostN/3, the output cannot exceedN. Write L = P≤N/3 and H = I−L . The telescoping
expansion isC(f1,f 2,f 3)−C (Lf1,Lf 2,Lf 3) =C(Hf1,f 2,f 3) +C(Lf1,Hf 2,f 3) +C(Lf1,Lf 2,Hf 3).
The low-input term has no output aboveN, and each projection contracts both components of
X(I). For the specified high input,∥Hfi∥H−p∗≤CN −p∗∥fi∥2. In (15), place theH−p∗ norm on
that input. Bernstein gives
∥P>NCI(f1,f 2,f 3)∥L2≤Ch
∏
j
∥fj∥X(I) +CN −p∗
∏
j
∥fj∥L∞(I;L 2).(32)
Applying (28) to the middle two terms of (31) yieldsCMhτγ +CM(h+N −p∗)EI.
The last term of(31) requires the stepwise formula forR′ in (25). On each intersected step it
becomes a sum of
−C(Yn,zn,V),− 1
2C(Yn,Yn,V),−τ −1
∫
Js(Wn,V)ds.
The first two areO(τqn)by (15), with the negative norm onYn, and(24), (28). The last isO(τqn)
by (21) and theL2 bound forJ. Even for a partial final step this is a valid upper bound. Summing
givesC M(h+τ)(τ γ +EI). Combining these facts,
sup
t∈I
∥P>NFI(t)∥L2≤C M(h+τ)τ γ +CM(h+τ+N −1 +N−p∗)EI.(33)
Equations (29), (27), (30), and (33) imply
EI≤∥e(a)∥ L2 +CM(h+τ)τ γ +CM
(
N 2h+h+τ+N −1 +N−p∗
)
EI.(34)
First fixN so large thatCM(N−1 +N−p∗)≤ 1/4. Next chooseδ∈ (0, 1]sufficiently small that
CMδ(N 2 + 3)≤ 1/4. Restrictτ≤δ/ 2. For intervals starting at grid points and having length at
mostδ, (34) gives
EI≤2∥e(a)∥ L2 +C′
Mδτγ.(35)
10

Use successive blocks of⌊δ/τ⌋ steps, whose lengths lie in[δ/2,δ ], with a possibly shorter final block.
The number of blocks is at most2T/δ + 1, independently ofτ. Iterating (35), starting withe(0) = 0,
yields
sup
0≤t≤T
∥e(t)∥L2≤C M,γ,Tτγ,(36)
as long as the bootstrap bound is in force. By continuity, if∥e∥L2 first reached one, the same block
argument up to that time would give an upper boundCM,γ,Tτγ. Choosingτ0 smaller so that this is
less than1/2gives a contradiction. Hence(36) holds on all of[0,T ]. The retained initial endpoint
in (31) is estimated byEI on each block, so the recurrence also applies whene(a)̸= 0.
For nonsmoothu0∈H γ, approximate it by real, mean-zero trigonometric polynomials with
uniformly bounded Hγ norm. Take u0,m = P≤mu0 so∥u0,m∥Hγ ≤R and∥u0,m−u 0∥2 → 0.
Section 2.1 gives a commonM and sup[0,T]∥um−u∥ 2≤C (T, 2R)∥u0,m−u 0∥2→ 0. For each fixed
τ and finite number of steps, the unmodified map(2) is continuous onL2: its factors contain inverse
derivatives, and theH1 algebra estimate controls the products; factors such asτ−1 are finite whenτ
is fixed. Thus its iterates converge inL2. IndeedFτ :L2→H 1 is a continuous quadratic map. The
first term ofHτ is a product of inverse derivatives; the second contains the continuous bilinear mean
P0(f 2); the third contains theH1 product( SsD−1f)3 followed byD−1; and the fourth contains
D−2Fτ(f)and D−1f, againH1 products followed byD−2. For fixedτ >0, all coefficients are finite.
Every term is continuous fromL2 to L2. Induction on the finite numberL of steps givesun
m→u n
at every grid point. Take the maximum over theseL + 1points and pass to the limit in(36); C,τ 0
are the same for allm. The estimates never involved a higher Sobolev norm of the approximating
data. FinallyS tn is unitary andV(tn) =S−tnun, so the grid-point error is exactly∥u(tn)−u n∥L2.
This proves Theorem 1.
5 Numerical experiments
The numerical library implements the displayed update with Fourier coefficients on−K,...,K .
Polynomial products are full linear convolutions. The quadratic stage has support through2K;
cubic terms retain support through3K. Only the completed step is projected to|k|≤K . ThusK
is a fixed spatial approximation parameter, independent ofτ. These finite computations are distinct
from the time-semidiscrete theorem. The routines use direct convolution for short arrays and padded
FFT convolution for longer arrays, with no circular aliasing in either path. A step costsO(KlogK )
with FFT products andO(K)working storage; retaining allL + 1states costs O(LK). The direct
triple sum forR2 costs O(N 3)time and working storage in the present verification implementation.
5.1 Inputs and reference checks
For each positive frequency1≤k≤N, the two global data families start from coefficients
bmixed
k =



1, k= 1,
−iN−1/2(k/N)−1/2−γ, N/2<k≤N,
0,otherwise,
bpower
k =k−1/2−γeiθk.
Set b−k =bk, b0 = 0, and rescale to∥u0∥Hγ = 2. Random angles are generated by NumPy’s default
generator with seed518, uniformly on[−π,π ]. The experiment usesT = 1/4, γ∈{ 0.1, 0.5, 1},
N = 8in both families, and alsoN = 16for mixed data atγ = 0.1, 1. In each caseK = 4N is held
fixed andL∈{16,32,64,128,256,512}.
11

Familyγ N E 512 E512/τγ dref/E512
mixed 0.1 8 1.649e-04 3.534e-04 3.034e-03
mixed 0.5 8 3.427e-05 1.551e-03 3.021e-03
mixed 1 8 2.636e-06 5.399e-03 3.009e-03
power 0.1 8 6.852e-05 1.469e-04 3.009e-03
power 0.5 8 7.284e-06 3.297e-04 2.987e-03
power 1 8 6.183e-07 1.266e-03 2.963e-03
mixed 0.1 16 1.412e-03 3.026e-03 8.696e-03
mixed 1 16 4.623e-06 9.468e-03 7.045e-03
Table 1: Finest coarse run,T = 1/4, L = 512, K = 4N. Here E512 is measured against the
16384-step reference;d ref compares the8192- and16384-step references. Norms usedx/(2π).
Reference trajectories use the same resolved update with8192and16384steps, stored at all
coarse grid times. LetEL be the maximum coarse-gridL2 difference from the finer reference, and
let dref be the maximum difference between the two reference resolutions. Every reported row
satisfies dref/EL < 0.01; the largest ratio is0.00870. This refinement comparison is an empirical
reference-quality check, not a rigorous upper bound on reference error.
Two further checks use the independent Galerkin ODEv′ =Bt(v,v )/2, solved with DOP853 [4].
The two solver tolerance pairs are(rtol,atol ) = (10−10, 10−12)and(2 · 10−12, 2· 10−14). For mixed
data at(γ,N,K ) = (0.1, 8, 32), the reference differences are8.39· 10−12 between ODE tolerances
and1.67· 10−7 between the tighter ODE and the finest Li–Wu reference. For power data at(1, 8, 32),
these values are3.29· 10−11 and6 .11· 10−10. The adaptive ODE shares the Fourier operators, but
uses a different time discretization.
For the two mixedN = 16cases, doubling K from64to128changes the reference in the full
common Fourier space by2.67· 10−12 at γ = 0.1and1 .72· 10−15 at γ = 1. The corresponding
changes in theL = 512numerical trajectory are1 .04· 10−11 and6 .12· 10−16. These are selected
spatial checks, not a uniform space-discretization estimate.
The recorded Apple Silicon runtime gives NumPylongdouble only 52 explicit mantissa bits, the
same as binary64; that dtype comparison does not supply extra precision. Actual 80-digit mpmath
checks are used instead for the phase covariance, including small and strongly imbalanced phases,
and for the complete step at two small timesteps. The test suite also compares a complete step
with an independent literal Fourier implementation, checks full intermediate support, FFT/direct
convolution, zero mean, reality and translation, and uses a smooth independent ODE refinement
example.
5.2 The cubic remainder
The local experiments use N∈ {4, 8, 16, 32}, τ = N−3, and coefficients bk = k−1/2−γeiθk for
1≤k≤N . The four phase choices areθk = 0(even), θk =−π/2(odd), θk =−π/2−τk 3/2(half
Airy), and random angles with seed518 +N. After adding conjugate negative frequencies, rescale
to∥f∥Hγ = 1. The exact multiplier is summed through output frequency3N, with its resonant
part and its absolute Fourier envelope retained separately.
Figure 2 reports all 48 local cases. The normalized remainder is bounded over the tested
bandwidths. For half-Airy odd data, the ratio of theL2 remainder norm to theL2 absolute-envelope
norm lies between0.999962and1 .000000. Thus these finite examples allow almost coherent addition
of Fourier terms. The proof uses the absolute envelope and does not require cancellation of this type.
At total resonance,β =−α andητ = 1−sinc2(τα/2), so the resonant remainder is generally nonzero.
12

10−3 10−2
10−4
10−3
10−2
τ
EL
γ= 0.1
mixed
power
10−3 10−2
10−5
10−4
10−3
τ
γ= 0.5
10−3 10−2
10−6
10−5
10−4
τ
γ= 1
Figure 1: Maximum grid error forN = 8, K = 32. Each curve uses the same initial datum and
spatial cutoff throughout the refinement. Faster convergence at fixed bandwidth is compatible with
the rough-data upper bound and does not establish its sharpness.
101 101.5
10−4
10−3
N
∥R2,τ∥2/τ 1+γ
γ= 0.1
even
odd
half airy
random
101 101.5
10−3
10−2
N
γ= 0.5
101 101.5
10−3
10−2
N
γ= 1
Figure 2: The normalized full cubic remainder for four phase families,∥f∥Hγ = 1and τ =N−3. All
output modes through3Nare included.
The bounded finite sample does not establish a uniform infinite-dimensional bound; Theorem 5
does.
5.3 Accumulation of defects and feedback
For a fixed coarse step letΨτ denote the implemented update and letrn be the finer reference attn.
Define
dn =r n+1−Ψτ(rn), g n = Ψτ(rn)−Ψ τ(un
K)−S τ(rn−un
K).
The grid erroren =r n−un
K therefore satisfies exactly
S−tmem =
m−1∑
n=0
S−tn+1dn +
m−1∑
n=0
S−tn+1gn.
The archives retain both sums and every individual Fourier defect and feedback. The largest
reconstruction discrepancy over all 48 global runs is3.93· 10−15. This identity is an accounting
check on the saved states, not an independent convergence estimate.
In the mixed(γ,N,K,L ) = (0.1, 16, 64, 16)example, the transported defect sum has coherence
∥∑S−tn+1dn∥2/∑∥dn∥2 = 0.99448at T. The errors and the two accumulated components appear
13

0 5·10 −2 0.1 0.15 0.2 0.25
0
2
4
·10−2
Time
L2 norm
error
transported defect
transported feedback
Figure 3: Error, transported defect sum, and transported feedback sum for mixed data withγ = 0.1,
N= 16,K= 64,L= 16. The two components are vector sums and their norms are not additive.
in Figure 3. At the peak error time, modesk =±1contain90 .68%of the error energy. Splitting
each modal energy as
|rk−uk|2 = (|rk|−|u k|)2 + 2|rk||uk|(1−cos(argr k−argu k))
gives a phase contribution of99.83%in that example. The second summand is defined as zero
when either magnitude is zero. Across the 48 global runs, the phase fraction at peak ranges from
86.48%to100 .00%, whereas the fraction in modes±1ranges from0 .81%to96 .77%. Low-mode
concentration is therefore case-dependent. The residual proof allows coherent accumulation and
does not assume statistically independent step errors.
The main campaign took 84.3 seconds and peaked at 390 MB resident memory on the recorded
single-thread local runtime. The accompanying submission package contains this article and its
editable source, the numerical library, tests, scripts, seeds, configurations, compact scalar summaries
and vector figures. Its README gives installation, test and experiment commands that regenerate
all complex Fourier checkpoints, step defects and reference comparisons. These generated arrays
remain in the local results directory and are excluded from version control. The theorem concerns
the exact time-semidiscrete update; a fully discrete uniform convergence theorem and a rate lower
bound are outside its scope.
14

References
[1] B. Li and Y. Wu,An Unfiltered Low-Regularity Integrator for the KdV Equation with So-
lutions Below H1, Foundations of Computational Mathematics26(2026), 1321–1380. DOI:
10.1007/s10208-025-09702-0. The equation, lemma, and page references in this article use the
50-page author manuscript athttps://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf.
[2] A.V.Babin, A.A.IlyinandE.S.Titi,On the regularization mechanism for the periodic Korteweg–
de Vries equation, arXiv:0910.1389v2(23October2010), https://arxiv.org/abs/0910.1389v2.
All theorem locators refer to this 42-page version.
[3]MColbrook/AIM ,518. Removing the logarithmic loss in the Li–Wu KdV integrator, fixed problem
statement at commitc9929805cece044705abaaebe1cebddac1ba11a6ofMColbrook/AIM.
[4] The SciPy community, scipy.integrate.solve_ivp documentation, https://docs.scipy
.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html , accessed 10
October 2026.
AI use declaration
ChatGPT was used to develop candidate arguments in the source research conversation. Codex
assisted with reconstructing that material, expanding and auditing the natural-language proof,
checking primary sources and citation applicability, rewriting the manuscript, and implementing
and testing the numerical experiments. A separate fresh-context AI review was used to look for
mathematical and evidential objections. These natural-language and computational checks do not
constitute formal verification or human peer review.
15