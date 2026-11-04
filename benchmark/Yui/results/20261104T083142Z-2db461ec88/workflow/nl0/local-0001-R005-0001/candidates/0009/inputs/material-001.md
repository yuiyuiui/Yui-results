<!-- Source-only checked transcription of original.pdf. Page markers follow the supplied PDF. -->

<!-- PDF page 1 -->

# Removing the logarithmic loss in the Li–Wu KdV integrator

Kaiwen Jin  
yui.ui.siki@gmail.com  
10 October 2026

## Abstract

Li and Wu proved that their unfiltered integrator for periodic KdV converges in \(L^2\) with error \(O(\tau^\gamma\log(1/\tau))\) for real, mean-zero \(H^\gamma\) data, \(0<\gamma\le1\). We remove the logarithmic factor for the same time-semidiscrete algorithm, with constants uniform on bounded \(H^\gamma\) sets. The main estimate concerns the exact averaged cubic remainder. Retaining both ratios of its two oscillatory phases bounds the dual four-frequency multiplier by the reciprocal of the third largest frequency. A dyadic four-linear estimate sums this majorant without a logarithm and includes a mixed \(L^2\) endpoint. That endpoint controls the remainder at the numerical state without a numerical Sobolev bound. We then prove the full global estimate using the continuous trilinear bounds of Li and Wu, a stepwise residual calculation, low–high frequency stability, a restarted bootstrap, and density. Finite Fourier experiments check the implemented update, the remainder, and accumulated step defects.

## 1 Introduction

Low spatial regularity limits the accuracy of time discretizations for dispersive equations. For periodic KdV, differentiation in the quadratic nonlinearity makes a direct \(L^2\) perturbation estimate insufficient. The unfiltered method of Li and Wu integrates the leading oscillatory interactions explicitly and treats its numerical trajectory as a perturbed KdV solution. Their convergence theorem gives \(C\tau^\gamma\log(1/\tau)\) in \(L^2\) for \(H^\gamma\) data with \(0<\gamma\le1\) [1, Theorem 1.1]. The necessity of the logarithm is left open in [1, Section 11]; this is the fixed-scheme question in AIM problem 518 [3].

We prove the bound \(C\tau^\gamma\) for that same method, uniformly on bounded sets of real, mean-zero \(H^\gamma\) data. The improvement comes from the averaging remainder, rather than a change in the update. Its multiplier contains the covariance of two exponential phases. Each phase can be integrated against the other, giving two ratio bounds. Keeping their minimum matters when the output frequency is small. After duality the four frequencies sum to zero, their largest two magnitudes are comparable, and the remaining multiplier is controlled by \(1/N_3\), where \(N_3\) is the third largest magnitude. The smaller dyadic scales then carry a summable geometric factor.

The resulting trilinear estimate includes exponent zero. This is a local remainder estimate: it does not assert a uniform global rate on an \(L^2\) ball. Its role is to compare the cubic remainder at the numerical state with the remainder at an exact \(H^\gamma\) state using only their \(L^2\) difference. We retain the continuous trilinear estimates of Li and Wu and give the residual and stability argument in full. In particular, the normal-form identity keeps both endpoints when the time interval is restarted, and its forcing term is estimated from the actual stepwise residual. A fixed-timestep approximation argument then removes the temporary smoothness used in the calculations.

The experiments use a fixed finite Fourier cutoff, complete polynomial intermediates, and independently checked reference resolutions. They illustrate the remainder and error accumulation.

<!-- PDF page 2 -->

Every computed input is a smooth Fourier polynomial, so these observations do not decide a uniform rough-data rate or the necessity of a logarithm; that conclusion is proved analytically below.

## 2 The scheme and the main result

Use normalized measure \(dx/(2\pi)\) on \(\mathbb T=\mathbb R/(2\pi\mathbb Z)\); changing to unnormalized \(L^2\) only changes constants. Write \(S_t=e^{-t\partial_x^3}\), so that \(\widehat{S_tf}(k)=e^{itk^3}\widehat f(k)\). Let \(P_0\) be the mean, \(P=I-P_0\), and define \(D^{-1}=\partial_x^{-1}\) with multiplier \((ik)^{-1}\) for \(k\ne0\) and zero at zero. Set \(D^{-2}=(D^{-1})^2\). Write
\[
\widehat f(k)=(2\pi)^{-1}\int_0^{2\pi}f(x)e^{-ikx}\,dx
\quad\hbox{and}\quad
\|f\|_{H^s}^2=\sum_{k\in\mathbb Z}\langle k\rangle^{2s}|\widehat f(k)|^2,
\qquad \langle k\rangle=(1+k^2)^{1/2}.
\]
Spaces are the completions of trigonometric polynomials in these norms, with negative spaces interpreted as distributions. Orthogonality gives the normalized \(L^2\) identity for polynomials and hence for their completions. For mean-zero functions and \(s\ge0\), \(\|f\|_{\dot H^s}\le\|f\|_{H^s}\le2^{s/2}\|f\|_{\dot H^s}\); for \(s<0\), \(2^{s/2}\|f\|_{\dot H^s}\le\|f\|_{H^s}\le\|f\|_{\dot H^s}\). Real-valued means \(\widehat f(-k)=\overline{\widehat f(k)}\). All time suprema concern continuous representatives; derivative norms are essential suprema. The exact solution is the unique real mean-zero \(C([0,T];H^\gamma)\) solution obtained by smooth approximation, and satisfies the equation distributionally. The constants \(C_M\) may change from line to line and depend on \(\gamma,T,M\), but are uniform in \(n,\tau\) and spectral support.

The equation is
\[
u_t+u_{xxx}=\tfrac12\partial_x(u^2),\qquad u(0)=u_0. \tag{1}
\]
The fixed scheme is \(u^0=u_0\) and
\[
u^{n+1}=S_\tau u^n+F_\tau(u^n)+H_\tau(u^n),\qquad \tau=T/L, \tag{2}
\]
where
\[
\begin{aligned}
F_\tau(f)&=\tfrac16 P[(S_\tau D^{-1}f)^2]-\tfrac16 S_\tau P[(D^{-1}f)^2],\\
H_\tau(f)&=\tfrac13 P[(S_\tau D^{-1}f)D^{-1}F_\tau(f)]
+\tfrac{\tau}{9}(S_\tau D^{-1}f)P_0(f^2)\\
&\quad-\tfrac1{54}\left[S_{\tau-s}D^{-1}[(S_sD^{-1}f)^3]\right]_{s=0}^{s=\tau}\\
&\quad-\tfrac1{27\tau}\left[S_{\tau-s}D^{-2}[(S_{s-\tau}D^{-2}F_\tau(f))(S_sD^{-1}f)]\right]_{s=0}^{s=\tau}.
\end{aligned}
\]
This is the scheme of [1, Eq. (1.4)], without a spatial frequency cutoff.

**Theorem 1 (Logarithm-free convergence).** Let \(T>0\), \(0<\gamma\le1\), and \(R>0\). For real, mean-zero \(u_0\in H^\gamma(\mathbb T)\) with \(\|u_0\|_{H^\gamma}\le R\), there are \(C,\tau_0>0\), depending only on \(T,\gamma,R\), such that the scheme (2) satisfies
\[
\max_{0\le n\le L}\|u(n\tau)-u^n\|_{L^2}\le C\tau^\gamma
\qquad\text{whenever }\tau=T/L\le\tau_0.
\]

The periodic KdV bounds of Babin–Ilyin–Titi control the exact flow on the initial-data ball. The continuous estimates of [1, Proposition 3.4 and Lemma 7.2] will be used in the stability proof. The logarithmic convergence theorem itself is not used. For the exact twisted solution \(v(t)=S_{-t}u(t)\), set
\[
M=1+\sup_{0\le t\le T}\|v(t)\|_{H^\gamma}.
\]
The source statements and the sign transformation giving a bound for \(M\) are recorded below in Section 2.1. No convergence theorem for the numerical scheme is used as an input. Intermediate constants may depend on \(M,\gamma,T\), but never on the timestep or a Fourier support bound.

<!-- PDF page 3 -->

### 2.1 The exact KdV flow

The source [2, Theorems 4.2–4.3, 5.1, 6.3–6.5] treats \(U_t=UU_x+U_{xxx}\) on the same torus, with normalized measure and mean-zero homogeneous Sobolev norms. Theorem 4.2 bounds its Galerkin flows on \([0,T]\) in \(\dot H^s\) by a constant depending only on \(s,T,\|U_0\|_{\dot H^s}\) and an upper bound for \(\|U_0\|_2\). Theorem 4.3 gives a distributional limiting solution with the same bound. Theorems 5.1 (\(s>1/2\)) and 6.3 (\(0<s\le1/2\)) give its uniqueness, \(C([0,T];\dot H^s)\) regularity and continuous dependence. Theorem 6.4 covers \(s=0\), and Theorem 6.5 with \(\theta=0\) states that, for two flows whose initial \(L^2\) norms sum to at most \(B\),
\(\sup_{[0,T]}\|U-\widetilde U\|_2\le C(T,B)\|U_0-\widetilde U_0\|_2\).
Together these results specify the continuous flow and the uniform bounds needed here.

Define \(u(t,x)=-U(t,-x)\). Then \(u_t=-U_t\), \(u_x=U_x\), \(u_{xxx}=U_{xxx}\) at \((t,-x)\), and consequently \(u_t+u_{xxx}=uu_x\). Fourier coefficients become \(\widehat u(k)=-\widehat U(-k)\), preserving every Sobolev norm, reality and zero mean. This transforms the source equation to (1). The norm comparison above transfers all bounds to our \(H^\gamma\) norm. Hence there is \(A(T,\gamma,R)<\infty\) such that every smooth initial datum in the stated ball satisfies \(\sup_{[0,T]}\|u(t)\|_{H^\gamma}\le A\). The same bound holds for the limiting solution: for each finite set of frequencies pass to the limit in its finite norm sum, then take the supremum over finite sets. Thus \(M\le1+A(T,\gamma,R)\) uniformly. Continuous dependence in \(L^2\) is precisely the input used in the final density passage. No change of torus length or amplitude scaling is needed.

## 3 The averaged cubic remainder

The estimate proved in this section is uniform in the Fourier support. We begin with the exact covariance in the update.

### 3.1 Covariance bounds

For real \(\alpha,\beta\) let
\[
M_\tau g=\frac1\tau\int_0^\tau g(s)\,ds,\qquad
\eta_\tau(\alpha,\beta)=M_\tau(e^{-is(\alpha+\beta)})
-M_\tau(e^{-is\alpha})M_\tau(e^{-is\beta}).
\]
For \(k=a+b+c\), put
\[
p=a+b,\qquad \alpha=3abp,\qquad \beta=3kcp,\qquad
\Phi=\alpha+\beta=k^3-a^3-b^3-c^3. \tag{3}
\]
In the notation of [1, Eqs. (4.15),(6.1)],
\[
\widehat{R^n_{2,\tau}(f_1,f_2,f_3)}(k)=
-\frac{\tau}{18ik}
\sum_{\substack{a+b+c=k\\a+b\ne0}}
e^{-it_n\Phi}\eta_\tau(\alpha,\beta)\widehat f_1(a)\widehat f_2(b)\widehat f_3(c),
\qquad k\ne0, \tag{4}
\]
with zero output at \(k=0\). Terms with a zero input frequency also vanish, because then \(\alpha=0\) or \(\beta=0\).

**Lemma 2 (Bounds for the average covariance).** If \(\alpha\beta\ne0\), then
\[
|\eta_\tau(\alpha,\beta)|\le2\min\{|\alpha/\beta|,|\beta/\alpha|\}, \tag{5}
\]
\[
|\eta_\tau(\alpha,\beta)|\le\tau\min\{|\alpha|,|\beta|\}. \tag{6}
\]
If either phase vanishes, \(\eta_\tau=0\).

<!-- PDF page 4 -->

*Proof.* Let \(h(s)=e^{-i\alpha s}-M_\tau(e^{-i\alpha s})\). Then \(\eta_\tau=\tau^{-1}\int_0^\tau h(s)e^{-i\beta s}\,ds\). The elementary bound
\(|h(s)|\le\tau^{-1}\int_0^\tau|\alpha||s-r|\,dr\le\tau|\alpha|\)
gives (6), also interchanging \(\alpha\) and \(\beta\). Moreover,
\[
|h(0)|+|h(\tau)|\le\tau|\alpha|,\qquad
\int_0^\tau|h'(s)|\,ds=\tau|\alpha|.
\]
Integrating \(e^{-i\beta s}\) once gives \(|\eta_\tau|\le2|\alpha/\beta|\). Interchanging the phases proves (5). These estimates are consistent with [1, Lemma 3.2]; the proof here records exactly which bounds will be retained. \(\square\)

### 3.2 Four frequencies and dyadic summation

For nonzero \(a,b,c,d\in\mathbb Z\) with \(a+b+c+d=0\), let \(N_1\ge N_2\ge N_3\ge N_4\) be the decreasing rearrangement of their absolute values. Thus \(N_3\) is the third largest, or second smallest, of *four* frequencies, including the dual output \(d=-k\). The zero-sum relation implies \(N_1\le3N_2\).

**Lemma 3 (Two pointwise majorants).** Write \(A=|ab|\) and \(B=|cd|\). Then
\[
\frac1{|d|}\min\{A/B,B/A\}\le\frac3{N_3}, \tag{7}
\]
\[
\frac{|a+b|}{\max(A,B)}\le\frac6{N_3}. \tag{8}
\]

*Proof.* For (7), if \(d\) is among the two largest frequencies, use \(\min(A/B,B/A)\le1\). Otherwise the largest two are among \(a,b,c\). If they are \(a,b\), then
\[
\frac1{|d|}\min(A/B,B/A)\le\frac{|c|}{|ab|}\le\frac1{N_3}.
\]
If they are \(a,c\) (the case \(b,c\) is identical), their ratio is between \(1/3\) and \(3\). The remaining magnitudes are \(|b|,|d|\), whose maximum is \(N_3\). Thus
\[
\frac1{|d|}\min(A/B,B/A)\le3\min\left\{\frac{|b|}{|d|^2},\frac1{|b|}\right\}
\le\frac3{\max(|b|,|d|)}.
\]
For (8), consider the pairing \((a,b)\) and \((c,d)\). If the two largest magnitudes are in the same pair, the other pair has sum of magnitude at most \(2N_3\). Since \(a+b=-(c+d)\),
\[
\frac{|a+b|}{\max(A,B)}\le\frac{2N_3}{N_1N_2}\le\frac2{N_3}.
\]
If the largest two belong to different pairs, the third largest is paired with one of them. Hence \(\max(A,B)\ge N_2N_3\) and \(|a+b|\le2N_1\le6N_2\), giving the result. Ties can be ordered arbitrarily; the same alternatives cover them. \(\square\)

**Lemma 4 (Third-largest-frequency four-linear estimate).** For nonnegative \(x_j\in\ell^2(\mathbb Z\setminus\{0\})\),
\[
\sum_{\substack{a+b+c+d=0\\abcd\ne0}}
\frac{x_1(a)x_2(b)x_3(c)x_4(d)}{N_3(a,b,c,d)}
\le C\prod_{j=1}^4\|x_j\|_{\ell^2}. \tag{9}
\]
The same conclusion holds after restricting the sum to any subset.

<!-- PDF page 5 -->

*Proof.* It suffices first to consider finitely supported sequences. Decompose into shells \(2^j\le|k|<2^{j+1}\), \(j\ge0\), and write \(X_{r,j}\) for the \(\ell^2\) norm of the \(r\)th sequence on the \(j\)th shell. Fix an ordering of the four shell indices \(j_1\ge j_2\ge j_3\ge j_4\). A nonzero zero-sum interaction has \(j_1-j_2\le2\). For each fixed pair of smaller-shell frequencies, the remaining sum of the two larger-shell sequences is at most their \(\ell^2\) norm product by Cauchy–Schwarz, since one sequence is a translated reflection of the other. Sum the smaller frequencies in \(\ell^1\). A shell has at most \(2^{j+1}\) integer elements, so another Cauchy–Schwarz bound gives
\[
\sum_{a+b+c+d=0}\prod_{r=1}^4 x_{r,j_r}
\le C2^{(j_3+j_4)/2}\prod_{r=1}^4 X_{r,j_r}.
\]
Since \(N_3\ge2^{j_3}\), the weight leaves \(C2^{-(j_3-j_4)/2}\). For \(q=j_1-j_2\in\{0,1,2\}\), extend the nonnegative sum by dropping the upper restriction on the smaller shells. The contribution is at most
\[
C\left(\sum_J X_{1,J}X_{2,J-q}\right)
\left(\sum_{\ell\ge m}2^{-(\ell-m)/2}X_{3,\ell}X_{4,m}\right).
\]
The first factor is bounded by Cauchy–Schwarz. Writing \(r=\ell-m\), the second is at most
\[
\sum_{r\ge0}2^{-r/2}\|X_3\|_{\ell^2}\|X_4\|_{\ell^2}
=\frac{\|X_3\|_{\ell^2}\|X_4\|_{\ell^2}}{1-2^{-1/2}}.
\]
Sum over at most 24 orderings and three offsets. For arbitrary nonnegative sequences apply the finite bound to their restrictions to \(|k|\le m\). The infinite positive sum is the supremum of these finite sums, while the norms of the restrictions are bounded by the full norms. This proves the infinite statement without exchanging conditionally convergent sums. \(\square\)

### 3.3 The mixed remainder estimate

**Theorem 5 (Mixed remainder bound).** For \(0\le\gamma\le1\), \(\tau>0\), and arbitrary mean-zero inputs \(f_j\in H^\gamma(\mathbb T)\),
\[
\|R^n_{2,\tau}(f_1,f_2,f_3)\|_{L^2}
\le C\tau^{1+\gamma}\prod_{j=1}^3\|f_j\|_{H^\gamma}, \tag{10}
\]
uniformly in \(n,\tau\), and Fourier support. The estimate remains true if an arbitrary multiplier of modulus at most one is inserted in the sum (4). In particular it holds separately on \(\Phi=0\) and \(\Phi\ne0\).

*Proof.* Only nonzero \(abck\) and \(p=a+b\ne0\) need consideration. Set \(d=-k\). Lemma 2 and (7) give
\[
\frac{|\eta|}{|k|}\le\frac6{N_3}.
\]
For the other endpoint, observe that \(AB=|abck|\), and use (6) and (8):
\[
\frac{|\eta|}{\tau|abck|}\le3\frac{|p|\min(A,B)}{AB}
=3\frac{|p|}{\max(A,B)}\le\frac{18}{N_3}.
\]
Taking the geometric mean of these two bounds yields
\[
\boxed{\frac{|\eta_\tau(\alpha,\beta)|}{|k||abc|^\gamma}
\le\frac{6^{1-\gamma}18^\gamma\tau^\gamma}{N_3(a,b,c,-k)}.} \tag{11}
\]

<!-- PDF page 6 -->

Dualize (4) against an \(\ell^2\) sequence and take absolute values. Apply Lemma 4 with \(x_1(a)=|a|^\gamma|\widehat f_1(a)|\) and analogously for \(x_2,x_3\); \(x_4(d)\) is the absolute value of the dual coefficient at \(-d\). Their norms are bounded by the inhomogeneous Sobolev norms and the dual norm. The factors \(e^{-it_n\Phi}\) have modulus one. This proves the theorem, including the assertion about restricted sums. Polynomial approximation and the bound extend the operator to the claimed spaces. \(\square\)

*Remark 6.* The exponent-zero assertion above is an estimate for the local cubic remainder, not a convergence theorem at \(\gamma=0\). The global closure below uses \(\gamma>0\).

**Corollary 7 (A numerical-state estimate).** Let \(w\in H^\gamma\), \(f\in L^2\), \(\|w\|_{H^\gamma}\le M\) and \(\delta=\|f-w\|_{L^2}\le1\). For \(0<\tau\le1\),
\[
\|R^n_{2,\tau}(f,f,f)\|_{L^2}\le C_M\tau(\tau^\gamma+\delta). \tag{12}
\]

*Proof.* Apply (10) with exponent \(\gamma\) to \((w,w,w)\). Expand the difference between the cubic expressions at \(f\) and at \(w\), and apply its exponent-zero case to every difference term. This gives \(C\tau\delta(\|f\|_{L^2}+\|w\|_{L^2})^2\). No \(H^\gamma\) bound on the numerical state is used. \(\square\)

## 4 Global convergence

### 4.1 Continuous estimates and normal forms

Fix \(p_*=23/14>3/2\) and, for an interval \(I\) of length at most one, set
\[
\|f\|_{X(I)}=\|f\|_{L^\infty(I;L^2)}+\|\partial_tf\|_{L^\infty(I;H^{-p_*})}.
\]
Define
\[
\begin{aligned}
\mathcal B_t(f,g)&=S_{-t}\partial_x[(S_tf)(S_tg)],\\
\mathcal J_t(f,g)&=S_{-t}P[(S_t\partial_x^{-1}f)(S_t\partial_x^{-1}g)],\\
C_I(f,g,h)&=\int_I S_{-t}P\{P[(S_tf)(S_tg)](S_t\partial_x^{-1}h)\}\,dt.
\end{aligned}
\]
The normal-form identity is
\[
\int_a^b\mathcal B_t(f,g)\,dt
=\tfrac13[\mathcal J_t(f,g)]_a^b
-\tfrac13\int_a^b\{\mathcal J_t(f',g)+\mathcal J_t(f,g')\}\,dt. \tag{13}
\]
For time-smooth, spatially smooth mean-zero functions, the coefficient of \(\mathcal J_t(f,g)\) at \(k\ne0\) is
\(\sum_{a+b=k}e^{-it3kab}(ia)^{-1}(ib)^{-1}\widehat f(a)\widehat g(b)\).
Differentiating the phase gives \(3ik\) times the product coefficients, hence
\(\partial_t\mathcal J_t(f,g)=3\mathcal B_t(f,g)+\mathcal J_t(f',g)+\mathcal J_t(f,g')\).
Integrating proves (13). Smooth functions have absolutely convergent Fourier sums, including every derivative appearing here. Piecewise smooth time dependence is sufficient after applying this calculation on each step. Since \(D^{-1}\partial_x=P\), the second identity below follows by substituting the definition of \(\mathcal B\); it does not require commutation through a product. Also \(\mathcal J_t\) is symmetric and
\[
\int_I\mathcal J_t(\mathcal B_t(f,g),h)\,dt=C_I(f,g,h). \tag{14}
\]
The following are the published inputs from [1, Proposition 3.4]:
\[
\|C_I(f_1,f_2,f_3)\|_{L^2}
\le C|I|\prod_j\|f_j\|_{X(I)}
+C\|f_i\|_{L^\infty H^{-p_*}}\prod_{j\ne i}\|f_j\|_{L^\infty L^2},
\qquad i=1,2,3, \tag{15}
\]
\[
\|C_I(f_1,f_2,f_3)\|_{L^2}
\le C_\alpha|I|^\alpha\prod_j\|f_j\|_{H^\alpha},
\qquad 0\le\alpha\le1,\quad f_j\text{ time-independent}. \tag{16}
\]

<!-- PDF page 7 -->

All time norms in (15) are over \(I\). The other input is the following consequence of [1, Lemma 7.2 and Eq. (2.2)]. There exists \(a_\gamma\in[0,1)\) such that
\[
\|fg\|_{L^2}\le C_\gamma\|f\|_{H^\gamma}\|g\|_{H^{a_\gamma}}, \tag{17}
\]
and, with \(F_n(t;w)=\tfrac12\int_{t_n}^t\mathcal B_s(w,w)\,ds\),
\[
\sup_{t_n\le t\le t_{n+1}}\|F_n(t;w)\|_{H^{a_\gamma}}\le C_M\tau^\gamma,\qquad
\sup_{t_n\le t\le t_{n+1}}\|F_n(t;w)\|_{H^{1+\gamma}}\le C_M, \tag{18}
\]
when \(\|w\|_{H^\gamma}\le M\). One can take \(a_\gamma=1/2-\gamma\) for \(0<\gamma<1/2\), \(1/8\) for \(\gamma=1/2\), and \(a_\gamma=0\) for \(\gamma>1/2\). For clarity, the source stage exponent is \(\theta=(1+\gamma-\beta)/(1+\gamma-\beta_0)\), with \(\beta_0=2\gamma-3/2\) for \(0<\gamma<1/2\), \(\beta_0=-1/2-\epsilon\) for \(\gamma=1/2\), and \(\beta_0=\gamma-1\) for \(1/2<\gamma\le1\). Take \(\epsilon=1/8\) in the middle case. At \(\beta=a_\gamma\) the exponents are respectively \((1/2+2\gamma)/(5/2-\gamma)\ge\gamma\), \(11/17>1/2\) and \((1+\gamma)/2\ge\gamma\). Every \(a_\gamma\) lies in the source interval \([\beta_0,1+\gamma]\). Since \(0<\tau\le1\), these exponents imply the first bound in (18). At \(\beta=1+\gamma\) the exponent is zero, giving the second. Inequality (17) is the source [1, Eqs. (2.2)–(2.3)], with the same fixed \(1/8\) choice when \(\gamma=1/2\). Source \(L^2\) and \(H^s\) norms are \(\sqrt{2\pi}\) times ours; dividing the source inequalities absorbs only fixed factors into constants. These estimates require no regularity beyond \(H^\gamma\) on \(w\). Finally the elementary one-dimensional bounds are
\[
\|\partial_x^{-1}f\|_{H^1}+\|\partial_x^{-1}f\|_{L^\infty}\lesssim\|f\|_{L^2},
\qquad
\|\mathcal B_t(f,g)\|_{H^{-p_*}}\lesssim\|f\|_{L^2}\|g\|_{L^2},
\qquad
\|\mathcal J_t(f,g)\|_{H^1}\lesssim\|f\|_{L^2}\|g\|_{L^2}. \tag{19}
\]
The second bound uses \(L^1(\mathbb T)\hookrightarrow H^{-p_*+1}(\mathbb T)\).

### 4.2 Elementary product bounds

Here are direct proofs of (19) and the variants used below. Cauchy–Schwarz in Fourier gives
\(\|D^{-1}f\|_\infty\le(\sum_{k\ne0}k^{-2})^{1/2}\|f\|_2\),
and \(\|D^{-1}f\|_{H^1}\le\sqrt2\|f\|_2\).
For \(A,B\in H^1\), the product rule and the preceding \(H^1\) to \(L^\infty\) bound give
\(\|AB\|_{H^1}\le C\|A\|_{H^1}\|B\|_{H^1}\).
Thus \(\|\mathcal J_t(f,g)\|_{H^1}\le C\|f\|_2\|g\|_2\).
Writing \(|\widehat{FG}(k)|\le\|F\|_2\|G\|_2\) yields
\(\|\mathcal B_t(f,g)\|_{H^{-p_*}}^2\le\|f\|_2^2\|g\|_2^2\sum_{k\ne0}k^2\langle k\rangle^{-2p_*}\).
The sum is finite exactly because \(p_*>3/2\). The same coefficient bound gives
\(\|D^{-1}P(FG)\|_2\le C\|F\|_2\|G\|_2\).
For a mean-zero \(A\), \(\|A\|_{H^{-p_*}}\le\|D^{-1}A\|_2\).
We also use the asymmetric bound
\(\|\mathcal J_t(A,B)\|_2\le C\|D^{-1}A\|_2\|B\|_2\):
bound the second inverse derivative in \(L^\infty\) and the first in \(L^2\).
All constants are uniform in \(t\), since \(S_t\) is an isometry in every Fourier Sobolev norm. Density extends the bounded products from polynomials.

### 4.3 The continuous numerical interpolation

Initially work with smooth data. All estimates below are independent of higher Sobolev norms; Section 4.4 removes this temporary device. Set \(v^n=S_{-t_n}u^n\) and on \(I_n=[t_n,t_{n+1}]\) write \(f=v^n\),

<!-- PDF page 8 -->

\(w=v(t_n)\), \(\delta_n=\|f-w\|_{L^2}\) and \(q_n=\tau^\gamma+\delta_n\). Assume \(\delta_n\le1\). Define
\[
\begin{aligned}
F_n(t)&=\tfrac12\int_{t_n}^t\mathcal B_s(f,f)\,ds,\qquad z_n(t)=f+F_n(t),\\
C_n(t)&=\int_{t_n}^t\mathcal B_s(f,F_n(s))\,ds,\\
Q_n(t)&=\tfrac12\int_{t_n}^t\mathcal B_s(F_n(s),F_n(s))\,ds,\\
W_n&=Q_n(t_{n+1})+R^n_{2,\tau}(f,f,f),\\
V(t)&=f+F_n(t)+C_n(t)+Q_n(t)-\frac{t-t_n}{\tau}W_n,\\
Y_n(t)&=V(t)-z_n(t).
\end{aligned}
\]
The source identity is \(v^{n+1}=f+F_n(t_{n+1})+C_n(t_{n+1})-R^n_{2,\tau}(f,f,f)\) ([1, Eqs. (4.20)–(4.23),(5.2)]); the \(Q_n(t_{n+1})\) terms in our definition cancel. The source notation \(e^{t\partial_x^3}\) is exactly our \(S_{-t}\), \(A^n\) is our \(C_n(t_{n+1})\), and source \(R_2^n\) is (4). Consequently the exact identity [1, Eqs. (5.2)–(5.4)] implies \(V(t_n)=v^n\) and \(V(t_{n+1})=v^{n+1}\) for the specified scheme. Thus \(V\) is continuous across the grid and agrees there with the twisted numerical trajectory.

**Stages and endpoint correction**

The endpoint formula \(F_n(t)=\tfrac16[\mathcal J_s(f,f)]_{t_n}^t\) gives
\[
\sup_{I_n}\|F_n(t)\|_{H^1}\le C_M,\qquad
\sup_{I_n}\|F_n(t)-F_n(t;w)\|_{H^1}\le C_M\delta_n.
\]
Together with (18), this yields
\[
\sup_{I_n}\|F_n(t)\|_{H^{a_\gamma}}+\sup_{I_n}\|F_n(t)\|_{L^2}\le C_Mq_n,
\qquad\|z_n\|_{X(I_n)}\le C_M. \tag{20}
\]
For the exact-data contribution, apply (17) to \(\partial_x(S_tF_n(t;w))\) and \(S_tF_n(t;w)\); use (18). Write \(A=F_n(t;w)\) and \(D=F_n(t)-A\). The exact-data term obeys
\(\|\partial_x[(S_tA)^2]\|_2\le2C_\gamma\|A\|_{H^{1+\gamma}}\|A\|_{H^{a_\gamma}}\le C_M\tau^\gamma\).
The difference of squares is \((S_tD)S_t(F_n+A)\); both second factors have bounded \(H^1\) norm and \(\|D\|_{H^1}\le C_M\delta_n\). The \(H^1\) algebra estimate bounds its derivative by \(C_M\delta_n\). Thus
\[
\sup_{I_n}\|\mathcal B_t(F_n(t),F_n(t))\|_{L^2}\le C_Mq_n.
\]
Consequently Corollary 7 implies
\[
\sup_{I_n}\|Q_n(t)\|_{L^2}+\|W_n\|_{L^2}\le C_M\tau q_n. \tag{21}
\]

**The interpolation defect**

To bound \(D^{-1}\mathcal B_t(f,F_n)\), use its exact expression \(S_{-t}P[(S_tf)(S_tF_n)]\). The product containing \(w\) is bounded by \(C_\gamma\|w\|_{H^\gamma}\|F_n\|_{H^{a_\gamma}}\). The product containing \(f-w\) is bounded by \(\|f-w\|_2\|S_tF_n\|_\infty\le C_M\delta_n\) using the uniform \(H^1\) bound. Therefore
\[
\sup_{I_n}\|\partial_x^{-1}\mathcal B_t(f,F_n(t))\|_{L^2}\le C_Mq_n.
\]

<!-- PDF page 9 -->

Use (21) and \(Y_n'=\mathcal B_t(f,F_n)+\tfrac12\mathcal B_t(F_n,F_n)-\tau^{-1}W_n\) to get
\[
\sup_{I_n}\|\partial_x^{-1}Y_n\|_{L^2}\le C_M\tau q_n,\qquad
\sup_{I_n}\|\partial_x^{-1}Y_n'\|_{L^2}\le C_Mq_n. \tag{22}
\]
For the strong norm, (13) and \(F_n'=\tfrac12\mathcal B_t(f,f)\) give exactly
\[
C_n(t)=\tfrac13\mathcal J_t(f,F_n(t))-\tfrac16C_{[t_n,t]}(f,f,f).
\]
The first term is \(O(q_n)\) in \(L^2\). In the second, use (16) with exponent \(\gamma\) on \((w,w,w)\), and exponent zero on every term in the difference with \((f,f,f)\). Thus
\[
\sup_{I_n}\|Y_n\|_{L^2}\le C_Mq_n. \tag{23}
\]
Since \(p_*>1\), (22)–(23) imply the important pair
\[
\|Y_n\|_{X(I_n)}\le C_Mq_n,\qquad
\sup_{I_n}\|Y_n\|_{H^{-p_*}}\le C_M\tau q_n. \tag{24}
\]

**The residual**

Define on a step
\[
\rho_n(t)=-\int_{t_n}^t\mathcal B_s(Y_n,z_n)\,ds
-\tfrac12\int_{t_n}^t\mathcal B_s(Y_n,Y_n)\,ds
-\frac{t-t_n}{\tau}W_n.
\]
Concatenate these increments into \(\mathcal R(t)\), with \(\mathcal R(0)=0\). Then
\[
V'=\tfrac12\mathcal B_t(V,V)+\mathcal R',\qquad
\mathcal R'=-\mathcal B_t(Y_n,z_n)-\tfrac12\mathcal B_t(Y_n,Y_n)-\tau^{-1}W_n. \tag{25}
\]
We claim
\[
\sup_{I_n}\|\rho_n\|_{L^2}\le C_M\tau q_n,\qquad
\|\mathcal R'\|_{L^\infty(I_n;H^{-p_*})}\le C_Mq_n. \tag{26}
\]
For the first integral in \(\rho_n\), apply (13). The boundary term and the term containing \(Y_n'\) are each \(O(\tau q_n)\) by (22) and \(\|z_n\|_{L^2}\lesssim1\). Since \(z_n'=\tfrac12\mathcal B_t(f,f)\), the remaining term is a constant multiple of \(C(f,f,Y_n)\). In (15), put the negative norm on \(Y_n\) and use (24); the result is also \(O(\tau q_n)\). For the second integral apply (13) with \(Y_n\) in both slots. Its boundary and derivative terms are \(O(\tau q_n^2)=O(\tau q_n)\) because \(q_n\le2\). The \(W_n\) term is controlled by (21). This proves the first claim. The second follows directly from (25), (19), (21), and (23).

### 4.4 Stability and completion of the proof

Set \(e=v-V\). On an interval \(I=[a,b]\) starting at a grid point, with \(h=b-a\le1\), let \(E_I=\sup_I\|e\|_{L^2}\) and assume \(E_I\le1\). The interval may end inside a step. The preceding bounds imply
\[
\sup_{a\le t\le b}\|\mathcal R(t)-\mathcal R(a)\|_{L^2}
\le C_M(h+\tau)(\tau^\gamma+E_I), \tag{27}
\]
\[
\|e\|_{X(I)}\le C_M(\tau^\gamma+E_I),\qquad
\|v\|_{X(I)}+\|V\|_{X(I)}\le C_M. \tag{28}
\]
Indeed \(e'=\mathcal B_t(e,v-e/2)-\mathcal R'\). There are at most \(h/\tau+1\) intersected steps, each starting with \(\delta_n\le E_I\), so (26) proves the first bound and the \(H^{-p_*}\) product estimate proves the second.

<!-- PDF page 10 -->

For any \(t\in I\), define \(\mathcal F_I(t)=\int_a^t\mathcal B_s(e,v-e/2)\,ds\). The exact error identity is
\[
e(t)=e(a)+\mathcal F_I(t)-(\mathcal R(t)-\mathcal R(a)). \tag{29}
\]
Choose a Fourier threshold \(N\ge2\) only in the proof. It is not part of the algorithm. The low frequencies satisfy
\[
\sup_{t\in I}\|P_{\le N}\mathcal F_I(t)\|_{L^2}\le C_MN^2hE_I. \tag{30}
\]
For example \(\|\partial_x^{-1}P(fg)\|_{L^2}\lesssim\|f\|_{L^2}\|g\|_{L^2}\), followed by the two-derivative Bernstein bound, proves (30).

For high frequencies, (13) gives, retaining *both* endpoints,
\[
\begin{aligned}
\mathcal F_I(t)
&=\tfrac13[\mathcal J_s(e,v-e/2)]_{s=a}^{s=t}
-\tfrac13C_{[a,t]}(e,v-e/2,V)-\tfrac16C_{[a,t]}(v,v,e)\\
&\quad+\tfrac13\int_a^t\mathcal J_s(\mathcal R',V)\,ds. \tag{31}
\end{aligned}
\]
For an explicit verification put \(g=v-e/2\). Then \(e'=\mathcal B(e,g)-\mathcal R'\) and \(g'=\tfrac12\mathcal B(v,v)-\tfrac12\mathcal B(e,g)+\tfrac12\mathcal R'\).
In the differentiated terms of (13), symmetry of \(\mathcal J\) gives \(C(e,g,g)-\tfrac12C(e,g,e)=C(e,g,V)\) because \(g-e/2=V\).
The remaining cubic term is \(\tfrac12C(v,v,e)\), and the forcing terms are
\(-\mathcal J(\mathcal R',g)+\tfrac12\mathcal J(e,\mathcal R')=-\mathcal J(\mathcal R',V)\).
Multiplication by \(-1/3\) yields exactly (31). The endpoint terms after \(P_{>N}\) are bounded by \(C_MN^{-1}E_I\) by the \(H^1\) bound for \(\mathcal J\) in (19).

We spell out how the high-output trilinear terms are estimated. If all three inputs have frequencies at most \(N/3\), the output cannot exceed \(N\). Write \(L=P_{\le N/3}\) and \(H=I-L\). The telescoping expansion is
\(C(f_1,f_2,f_3)-C(Lf_1,Lf_2,Lf_3)=C(Hf_1,f_2,f_3)+C(Lf_1,Hf_2,f_3)+C(Lf_1,Lf_2,Hf_3)\).
The low-input term has no output above \(N\), and each projection contracts both components of \(X(I)\). For the specified high input, \(\|Hf_i\|_{H^{-p_*}}\le CN^{-p_*}\|f_i\|_2\). In (15), place the \(H^{-p_*}\) norm on that input. Bernstein gives
\[
\|P_{>N}C_I(f_1,f_2,f_3)\|_{L^2}
\le Ch\prod_j\|f_j\|_{X(I)}+CN^{-p_*}\prod_j\|f_j\|_{L^\infty(I;L^2)}. \tag{32}
\]
Applying (28) to the middle two terms of (31) yields \(C_Mh\tau^\gamma+C_M(h+N^{-p_*})E_I\).

The last term of (31) requires the stepwise formula for \(\mathcal R'\) in (25). On each intersected step it becomes a sum of
\[
-C(Y_n,z_n,V),\qquad-\tfrac12C(Y_n,Y_n,V),\qquad
-\tau^{-1}\int\mathcal J_s(W_n,V)\,ds.
\]
The first two are \(O(\tau q_n)\) by (15), with the negative norm on \(Y_n\), and (24), (28). The last is \(O(\tau q_n)\) by (21) and the \(L^2\) bound for \(\mathcal J\). Even for a partial final step this is a valid upper bound. Summing gives \(C_M(h+\tau)(\tau^\gamma+E_I)\). Combining these facts,
\[
\sup_{t\in I}\|P_{>N}\mathcal F_I(t)\|_{L^2}
\le C_M(h+\tau)\tau^\gamma+C_M(h+\tau+N^{-1}+N^{-p_*})E_I. \tag{33}
\]
Equations (29), (27), (30), and (33) imply
\[
E_I\le\|e(a)\|_{L^2}+C_M(h+\tau)\tau^\gamma+
C_M(N^2h+h+\tau+N^{-1}+N^{-p_*})E_I. \tag{34}
\]
First fix \(N\) so large that \(C_M(N^{-1}+N^{-p_*})\le1/4\).
Next choose \(\delta\in(0,1]\) sufficiently small that \(C_M\delta(N^2+3)\le1/4\).
Restrict \(\tau\le\delta/2\). For intervals starting at grid points and having length at most \(\delta\), (34) gives
\[
E_I\le2\|e(a)\|_{L^2}+C_M'\delta\tau^\gamma. \tag{35}
\]

<!-- PDF page 11 -->

Use successive blocks of \(\lfloor\delta/\tau\rfloor\) steps, whose lengths lie in \([\delta/2,\delta]\), with a possibly shorter final block. The number of blocks is at most \(2T/\delta+1\), independently of \(\tau\). Iterating (35), starting with \(e(0)=0\), yields
\[
\sup_{0\le t\le T}\|e(t)\|_{L^2}\le C_{M,\gamma,T}\tau^\gamma, \tag{36}
\]
as long as the bootstrap bound is in force. By continuity, if \(\|e\|_{L^2}\) first reached one, the same block argument up to that time would give an upper bound \(C_{M,\gamma,T}\tau^\gamma\). Choosing \(\tau_0\) smaller so that this is less than \(1/2\) gives a contradiction. Hence (36) holds on all of \([0,T]\). The retained initial endpoint in (31) is estimated by \(E_I\) on each block, so the recurrence also applies when \(e(a)\ne0\).

For nonsmooth \(u_0\in H^\gamma\), approximate it by real, mean-zero trigonometric polynomials with uniformly bounded \(H^\gamma\) norm. Take \(u_{0,m}=P_{\le m}u_0\) so \(\|u_{0,m}\|_{H^\gamma}\le R\) and \(\|u_{0,m}-u_0\|_2\to0\).
Section 2.1 gives a common \(M\) and \(\sup_{[0,T]}\|u_m-u\|_2\le C(T,2R)\|u_{0,m}-u_0\|_2\to0\).
For each fixed \(\tau\) and finite number of steps, the unmodified map (2) is continuous on \(L^2\): its factors contain inverse derivatives, and the \(H^1\) algebra estimate controls the products; factors such as \(\tau^{-1}\) are finite when \(\tau\) is fixed. Thus its iterates converge in \(L^2\). Indeed \(F_\tau:L^2\to H^1\) is a continuous quadratic map. The first term of \(H_\tau\) is a product of inverse derivatives; the second contains the continuous bilinear mean \(P_0(f^2)\); the third contains the \(H^1\) product \((S_sD^{-1}f)^3\) followed by \(D^{-1}\); and the fourth contains \(D^{-2}F_\tau(f)\) and \(D^{-1}f\), again \(H^1\) products followed by \(D^{-2}\). For fixed \(\tau>0\), all coefficients are finite. Every term is continuous from \(L^2\) to \(L^2\). Induction on the finite number \(L\) of steps gives \(u_m^n\to u^n\) at every grid point. Take the maximum over these \(L+1\) points and pass to the limit in (36); \(C,\tau_0\) are the same for all \(m\). The estimates never involved a higher Sobolev norm of the approximating data. Finally \(S_{t_n}\) is unitary and \(V(t_n)=S_{-t_n}u^n\), so the grid-point error is exactly \(\|u(t_n)-u^n\|_{L^2}\).
This proves Theorem 1.

## 5 Numerical experiments

The numerical library implements the displayed update with Fourier coefficients on \(-K,\ldots,K\). Polynomial products are full linear convolutions. The quadratic stage has support through \(2K\); cubic terms retain support through \(3K\). Only the completed step is projected to \(|k|\le K\). Thus \(K\) is a fixed spatial approximation parameter, independent of \(\tau\). These finite computations are distinct from the time-semidiscrete theorem. The routines use direct convolution for short arrays and padded FFT convolution for longer arrays, with no circular aliasing in either path. A step costs \(O(K\log K)\) with FFT products and \(O(K)\) working storage; retaining all \(L+1\) states costs \(O(LK)\). The direct triple sum for \(R_2\) costs \(O(N^3)\) time and working storage in the present verification implementation.

### 5.1 Inputs and reference checks

For each positive frequency \(1\le k\le N\), the two global data families start from coefficients
\[
b_k^{\rm mixed}=
\begin{cases}
1,&k=1,\\
-iN^{-1/2}(k/N)^{-1/2-\gamma},&N/2<k\le N,\\
0,&\text{otherwise},
\end{cases}
\qquad b_k^{\rm power}=k^{-1/2-\gamma}e^{i\theta_k}.
\]
Set \(b_{-k}=\overline{b_k}\), \(b_0=0\), and rescale to \(\|u_0\|_{H^\gamma}=2\).
Random angles are generated by NumPy's default generator with seed 518, uniformly on \([-\pi,\pi]\).
The experiment uses \(T=1/4\), \(\gamma\in\{0.1,0.5,1\}\), \(N=8\) in both families, and also \(N=16\) for mixed data at \(\gamma=0.1,1\).
In each case \(K=4N\) is held fixed and \(L\in\{16,32,64,128,256,512\}\).

<!-- PDF page 12 -->

| Family | \(\gamma\) | \(N\) | \(E_{512}\) | \(E_{512}/\tau^\gamma\) | \(d_{\rm ref}/E_{512}\) |
| --- | --- | --- | --- | --- | --- |
| mixed | 0.1 | 8 | 1.649e-04 | 3.534e-04 | 3.034e-03 |
| mixed | 0.5 | 8 | 3.427e-05 | 1.551e-03 | 3.021e-03 |
| mixed | 1 | 8 | 2.636e-06 | 5.399e-03 | 3.009e-03 |
| power | 0.1 | 8 | 6.852e-05 | 1.469e-04 | 3.009e-03 |
| power | 0.5 | 8 | 7.284e-06 | 3.297e-04 | 2.987e-03 |
| power | 1 | 8 | 6.183e-07 | 1.266e-03 | 2.963e-03 |
| mixed | 0.1 | 16 | 1.412e-03 | 3.026e-03 | 8.696e-03 |
| mixed | 1 | 16 | 4.623e-06 | 9.468e-03 | 7.045e-03 |

Table 1: Finest coarse run, \(T=1/4\), \(L=512\), \(K=4N\). Here \(E_{512}\) is measured against the 16384-step reference; \(d_{\rm ref}\) compares the 8192- and 16384-step references. Norms use \(dx/(2\pi)\).

Reference trajectories use the same resolved update with 8192 and 16384 steps, stored at all coarse grid times. Let \(E_L\) be the maximum coarse-grid \(L^2\) difference from the finer reference, and let \(d_{\rm ref}\) be the maximum difference between the two reference resolutions. Every reported row satisfies \(d_{\rm ref}/E_L<0.01\); the largest ratio is 0.00870. This refinement comparison is an empirical reference-quality check, not a rigorous upper bound on reference error.

Two further checks use the independent Galerkin ODE \(v'=\mathcal B_t(v,v)/2\), solved with DOP853 [4].
The two solver tolerance pairs are \((\mathrm{rtol},\mathrm{atol})=(10^{-10},10^{-12})\) and \((2\cdot10^{-12},2\cdot10^{-14})\).
For mixed data at \((\gamma,N,K)=(0.1,8,32)\), the reference differences are \(8.39\cdot10^{-12}\) between ODE tolerances and \(1.67\cdot10^{-7}\) between the tighter ODE and the finest Li–Wu reference.
For power data at \((1,8,32)\), these values are \(3.29\cdot10^{-11}\) and \(6.11\cdot10^{-10}\).
The adaptive ODE shares the Fourier operators, but uses a different time discretization.

For the two mixed \(N=16\) cases, doubling \(K\) from 64 to 128 changes the reference in the full common Fourier space by \(2.67\cdot10^{-12}\) at \(\gamma=0.1\) and \(1.72\cdot10^{-15}\) at \(\gamma=1\).
The corresponding changes in the \(L=512\) numerical trajectory are \(1.04\cdot10^{-11}\) and \(6.12\cdot10^{-16}\).
These are selected spatial checks, not a uniform space-discretization estimate.

The recorded Apple Silicon runtime gives NumPy longdouble only 52 explicit mantissa bits, the same as binary64; that dtype comparison does not supply extra precision. Actual 80-digit mpmath checks are used instead for the phase covariance, including small and strongly imbalanced phases, and for the complete step at two small timesteps. The test suite also compares a complete step with an independent literal Fourier implementation, checks full intermediate support, FFT/direct convolution, zero mean, reality and translation, and uses a smooth independent ODE refinement example.

### 5.2 The cubic remainder

The local experiments use \(N\in\{4,8,16,32\}\), \(\tau=N^{-3}\), and coefficients \(b_k=k^{-1/2-\gamma}e^{i\theta_k}\) for \(1\le k\le N\).
The four phase choices are \(\theta_k=0\) (even), \(\theta_k=-\pi/2\) (odd), \(\theta_k=-\pi/2-\tau k^3/2\) (half Airy), and random angles with seed \(518+N\).
After adding conjugate negative frequencies, rescale to \(\|f\|_{H^\gamma}=1\).
The exact multiplier is summed through output frequency \(3N\), with its resonant part and its absolute Fourier envelope retained separately.

Figure 2 reports all 48 local cases. The normalized remainder is bounded over the tested bandwidths.
For half-Airy odd data, the ratio of the \(L^2\) remainder norm to the \(L^2\) absolute-envelope norm lies between 0.999962 and 1.000000. Thus these finite examples allow almost coherent addition of Fourier terms.
The proof uses the absolute envelope and does not require cancellation of this type.
At total resonance, \(\beta=-\alpha\) and \(\eta_\tau=1-\operatorname{sinc}^2(\tau\alpha/2)\), so the resonant remainder is generally nonzero.

<!-- PDF page 13 -->

<!-- Figure 1 graphic: original.pdf, page 13, upper panel; retained in pages/page-13.png. Three panels gamma=0.1, 0.5, 1; horizontal axis tau, vertical axis E_L; legends mixed and power. -->

Figure 1: Maximum grid error for \(N=8\), \(K=32\). Each curve uses the same initial datum and spatial cutoff throughout the refinement. Faster convergence at fixed bandwidth is compatible with the rough-data upper bound and does not establish its sharpness.

<!-- Figure 2 graphic: original.pdf, page 13, middle panel; retained in pages/page-13.png. Three panels gamma=0.1, 0.5, 1; horizontal axis N, vertical axis ||R_{2,tau}||_2/tau^{1+gamma}; legends even, odd, half airy, random. -->

Figure 2: The normalized full cubic remainder for four phase families, \(\|f\|_{H^\gamma}=1\) and \(\tau=N^{-3}\). All output modes through \(3N\) are included.

The bounded finite sample does not establish a uniform infinite-dimensional bound; Theorem 5 does.

### 5.3 Accumulation of defects and feedback

For a fixed coarse step let \(\Psi_\tau\) denote the implemented update and let \(r_n\) be the finer reference at \(t_n\). Define
\[
d_n=r_{n+1}-\Psi_\tau(r_n),\qquad
g_n=\Psi_\tau(r_n)-\Psi_\tau(u_K^n)-S_\tau(r_n-u_K^n).
\]
The grid error \(e_n=r_n-u_K^n\) therefore satisfies exactly
\[
S_{-t_m}e_m=\sum_{n=0}^{m-1}S_{-t_{n+1}}d_n+
\sum_{n=0}^{m-1}S_{-t_{n+1}}g_n.
\]
The archives retain both sums and every individual Fourier defect and feedback.
The largest reconstruction discrepancy over all 48 global runs is \(3.93\cdot10^{-15}\).
This identity is an accounting check on the saved states, not an independent convergence estimate.

In the mixed \((\gamma,N,K,L)=(0.1,16,64,16)\) example, the transported defect sum has coherence
\(\|\sum S_{-t_{n+1}}d_n\|_2/\sum\|d_n\|_2=0.99448\) at \(T\).
The errors and the two accumulated components appear

<!-- PDF page 14 -->

<!-- Figure 3 graphic: original.pdf, page 14, upper panel; retained in pages/page-14.png. Horizontal axis Time; vertical axis L^2 norm; legends error, transported defect, transported feedback. -->

Figure 3: Error, transported defect sum, and transported feedback sum for mixed data with \(\gamma=0.1\), \(N=16\), \(K=64\), \(L=16\). The two components are vector sums and their norms are not additive.

in Figure 3. At the peak error time, modes \(k=\pm1\) contain 90.68% of the error energy. Splitting each modal energy as
\[
|r_k-u_k|^2=(|r_k|-|u_k|)^2+
2|r_k||u_k|(1-\cos(\arg r_k-\arg u_k))
\]
gives a phase contribution of 99.83% in that example. The second summand is defined as zero when either magnitude is zero. Across the 48 global runs, the phase fraction at peak ranges from 86.48% to 100.00%, whereas the fraction in modes \(\pm1\) ranges from 0.81% to 96.77%. Low-mode concentration is therefore case-dependent. The residual proof allows coherent accumulation and does not assume statistically independent step errors.

The main campaign took 84.3 seconds and peaked at 390 MB resident memory on the recorded single-thread local runtime. The accompanying submission package contains this article and its editable source, the numerical library, tests, scripts, seeds, configurations, compact scalar summaries and vector figures. Its README gives installation, test and experiment commands that regenerate all complex Fourier checkpoints, step defects and reference comparisons. These generated arrays remain in the local results directory and are excluded from version control. The theorem concerns the exact time-semidiscrete update; a fully discrete uniform convergence theorem and a rate lower bound are outside its scope.

<!-- PDF page 15 -->

## References

[1] B. Li and Y. Wu, *An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below \(H^1\)*, Foundations of Computational Mathematics **26** (2026), 1321–1380. DOI: 10.1007/s10208-025-09702-0. The equation, lemma, and page references in this article use the 50-page author manuscript at https://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf.

[2] A. V. Babin, A. A. Ilyin and E. S. Titi, *On the regularization mechanism for the periodic Korteweg–de Vries equation*, arXiv:0910.1389v2 (23 October 2010), https://arxiv.org/abs/0910.1389v2. All theorem locators refer to this 42-page version.

[3] MColbrook/AIM, *518. Removing the logarithmic loss in the Li–Wu KdV integrator*, fixed problem statement at commit c9929805cece044705abaaebe1cebddac1ba11a6 of MColbrook/AIM.

[4] The SciPy community, *scipy.integrate.solve_ivp documentation*, https://docs.scipy.org/doc/scipy/reference/generated/scipy.integrate.solve_ivp.html, accessed 10 October 2026.

## AI use declaration

ChatGPT was used to develop candidate arguments in the source research conversation. Codex assisted with reconstructing that material, expanding and auditing the natural-language proof, checking primary sources and citation applicability, rewriting the manuscript, and implementing and testing the numerical experiments. A separate fresh-context AI review was used to look for mathematical and evidential objections. These natural-language and computational checks do not constitute formal verification or human peer review.
