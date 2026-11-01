# Source-only checked mathematical transcription

Sole source: `aim-518-kdv-log-loss.pdf`, SHA-256 `5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6`.
This is notation readback of the supplied PDF, not an additional proof, review, or source. The ordinary pypdf extraction flattens fractions, scripts, hats and conjugation bars. The formulas below were checked against rendered original pages 2–11. The original extracted prose remains part of the input. Formula numbers and page numbers refer to that original. No external paper was retrieved by the owner before dispatch.

## Page 2: complete selected statement and standing definitions

Theorem 1 (Logarithm-free convergence), with the standing definitions of Section 2 of the supplied paper.

Use normalized measure dx/(2*pi) on the torus \mathbb{T} = \mathbb{R}/(2*pi \mathbb{Z}). The Fourier coefficient is
\hat f(k)=(2*pi)^(-1) integral_0^(2*pi) f(x) exp(-i*k*x) dx,
and ||f||_(H^s)^2=sum_(k in Z) <k>^(2s)|\hat f(k)|^2, where <k>=(1+k^2)^(1/2).
These spaces are the completions of trigonometric polynomials in these norms; negative spaces are interpreted as distributions. The normalized L^2 norm is the s=0 norm. For mean-zero functions, the homogeneous norm uses |k|^(2s) in place of <k>^(2s). For s>=0,
||f||_(dot H^s)<=||f||_(H^s)<=2^(s/2)||f||_(dot H^s);
for s<0, 2^(s/2)||f||_(dot H^s)<=||f||_(H^s)<=||f||_(dot H^s).
Real-valued means \hat f(-k)=overline(\hat f(k)), and mean-zero means \hat f(0)=0.
All time suprema concern continuous representatives; derivative norms are essential suprema.

Let S_t=exp(-t*partial_x^3), so \widehat{S_t f}(k)=exp(i*t*k^3)\hat f(k).
Let P_0 be the mean and P=I-P_0. Let D^(-1)=partial_x^(-1) have multiplier (i*k)^(-1) for k!=0 and zero at k=0; D^(-2)=(D^(-1))^2.
The equation is
u_t+u_xxx=(1/2)partial_x(u^2),  u(0)=u_0. [Eq. (1)]
The exact solution u is the unique real, mean-zero C([0,T];H^gamma) solution obtained by smooth approximation and satisfies this equation distributionally.

For a positive integer L and tau=T/L, the fixed time-semidiscrete scheme is u^0=u_0 and
u^(n+1)=S_tau u^n+F_tau(u^n)+H_tau(u^n), 0<=n<L, [Eq. (2)]
where
F_tau(f)=(1/6)P[(S_tau D^(-1)f)^2]-(1/6)S_tau P[(D^(-1)f)^2],
H_tau(f)=(1/3)P[(S_tau D^(-1)f)D^(-1)F_tau(f)]
 +(tau/9)(S_tau D^(-1)f)P_0(f^2)
 -(1/54)[S_(tau-s)D^(-1)[(S_s D^(-1)f)^3]]_(s=0)^(s=tau)
 -(1/(27*tau))[S_(tau-s)D^(-2)[(S_(s-tau)D^(-2)F_tau(f))(S_s D^(-1)f)]]_(s=0)^(s=tau).
Each bracket [G(s)]_(s=0)^(s=tau) means G(tau)-G(0).
This is the fixed scheme of the paper's reference [1, Eq. (1.4)], without a spatial frequency cutoff.

For every T>0, every 0<gamma<=1 and every R>0, there exist C>0 and tau_0>0 depending only on T,gamma,R such that, for every real, mean-zero u_0 in H^gamma(\mathbb{T}) with ||u_0||_(H^gamma)<=R and every positive integer L with tau=T/L<=tau_0, this exact fixed scheme satisfies
max_(0<=n<=L) ||u(n*tau)-u^n||_(L^2)<=C*tau^gamma.
The same C and tau_0 apply to the entire stated initial-data ball; no spectral support bound or additional smoothness is a hypothesis.

In the source's standing notation v(t)=S_(-t)u(t) and M=1+sup_(0<=t<=T)||v(t)||_(H^gamma).
Constants C_M may vary from line to line and depend on gamma,T,M, but are uniform in n,tau and spectral support. Section 2.1 supplies M<=1+A(T,gamma,R) uniformly on the ball using the cited exact-flow results; it is not an extra hypothesis on u_0. The source uses the continuous estimates from [1, Proposition 3.4 and Lemma 7.2] and does not use the logarithmic convergence theorem as an input.


## Page 3: original definitions and formulas (3)–(6)

For real alpha,beta,
M_tau g=(1/tau) integral_0^tau g(s) ds,
eta_tau(alpha,beta)=M_tau(exp(-i*s*(alpha+beta)))-M_tau(exp(-i*s*alpha))*M_tau(exp(-i*s*beta)).
For k=a+b+c,
p=a+b, alpha=3*a*b*p, beta=3*k*c*p, Phi=alpha+beta=k^3-a^3-b^3-c^3. (3)
For k!=0,
\widehat{R^n_(2,tau)(f_1,f_2,f_3)}(k)
 =-tau/(18*i*k) sum_(a+b+c=k, a+b!=0) exp(-i*t_n*Phi)*eta_tau(alpha,beta)*\hat f_1(a)*\hat f_2(b)*\hat f_3(c), (4)
with zero output at k=0. Terms with a zero input frequency vanish because then alpha=0 or beta=0.
Lemma 2: if alpha*beta!=0,
|eta_tau(alpha,beta)|<=2*min{|alpha/beta|,|beta/alpha|}, (5)
|eta_tau(alpha,beta)|<=tau*min{|alpha|,|beta|}. (6)
If either phase vanishes, eta_tau=0.

## Pages 4–5: (7)–(11)

For nonzero integers a,b,c,d with a+b+c+d=0, let N_1>=N_2>=N_3>=N_4 be the decreasing rearrangement of their absolute values. N_3 is third largest among all four, including d=-k. N_1<=3*N_2. Put A=|a*b|, B=|c*d|.
(1/|d|)*min{A/B,B/A}<=3/N_3. (7)
|a+b|/max(A,B)<=6/N_3. (8)
For nonnegative x_j in ell^2(Z\{0}),
sum_(a+b+c+d=0, a*b*c*d!=0) x_1(a)*x_2(b)*x_3(c)*x_4(d)/N_3(a,b,c,d)
 <=C*product_(j=1)^4 ||x_j||_(ell^2). (9)
The same conclusion holds after restricting the sum to any subset.

Page 5's shell proof uses 2^j<=|k|<2^(j+1), j>=0, X_(r,j) the ell^2 norm on the jth shell, ordered shell indices j_1>=j_2>=j_3>=j_4, and j_1-j_2<=2 for a nonzero interaction. Its displayed shell bound is
sum_(a+b+c+d=0) product_(r=1)^4 x_(r,j_r)
 <=C*2^((j_3+j_4)/2)*product_(r=1)^4 X_(r,j_r).
After the N_3 weight, the factor is C*2^(-(j_3-j_4)/2). For q=j_1-j_2 in {0,1,2}, the displayed bound is
C*(sum_J X_(1,J)*X_(2,J-q))*(sum_(ell>=m) 2^(-(ell-m)/2)*X_(3,ell)*X_(4,m)).
The latter factor is bounded by
sum_(r>=0) 2^(-r/2)*||X_3||_(ell^2)*||X_4||_(ell^2)
 =||X_3||_(ell^2)*||X_4||_(ell^2)/(1-2^(-1/2)).

Theorem 5 (Mixed remainder bound): for 0<=gamma<=1, tau>0, arbitrary mean-zero f_j in H^gamma(\mathbb{T}),
||R^n_(2,tau)(f_1,f_2,f_3)||_(L^2)<=C*tau^(1+gamma)*product_(j=1)^3 ||f_j||_(H^gamma), (10)
uniformly in n,tau and Fourier support. An arbitrary multiplier of modulus at most one may be inserted in (4); in particular the estimate holds separately on Phi=0 and Phi!=0.
The two endpoint bounds in its proof are |eta|/|k|<=6/N_3 and |eta|/(tau*|a*b*c*k|)<=18/N_3. Their displayed geometric-mean bound is
|eta_tau(alpha,beta)|/(|k|*|a*b*c|^gamma)
 <=6^(1-gamma)*18^gamma*tau^gamma/N_3(a,b,c,-k). (11)

## Page 6: (12)–(16) and the defined operators

Corollary 7: let w in H^gamma, f in L^2, ||w||_(H^gamma)<=M and delta=||f-w||_(L^2)<=1. For 0<tau<=1,
||R^n_(2,tau)(f,f,f)||_(L^2)<=C_M*tau*(tau^gamma+delta). (12)
Remark 6 states that the exponent-zero assertion is a local cubic remainder estimate; the global proof uses gamma>0.

Fix p_*=23/14>3/2. For an interval I of length at most one,
||f||_(X(I))=||f||_(L^infinity(I;L^2))+||partial_t f||_(L^infinity(I;H^(-p_*))).
B_t(f,g)=S_(-t) partial_x[(S_t f)(S_t g)],
J_t(f,g)=S_(-t)P[(S_t partial_x^(-1)f)(S_t partial_x^(-1)g)],
C_I(f,g,h)=integral_I S_(-t)P{P[(S_t f)(S_t g)](S_t partial_x^(-1)h)} dt.
The normal-form identity, for smooth mean-zero inputs and also stepwise for piecewise smooth time dependence, is
integral_a^b B_t(f,g) dt=(1/3)[J_t(f,g)]_a^b
 -(1/3)integral_a^b {J_t(f',g)+J_t(f,g')} dt. (13)
The nonzero kth Fourier coefficient of J_t is sum_(a+b=k) exp(-i*t*3*k*a*b)*(i*a)^(-1)*(i*b)^(-1)*\hat f(a)*\hat g(b).
J_t is symmetric, D^(-1)partial_x=P, and
integral_I J_t(B_t(f,g),h) dt=C_I(f,g,h). (14)
The published inputs attributed in the original to [1, Proposition 3.4] are
||C_I(f_1,f_2,f_3)||_(L^2)
 <=C*|I|*product_j ||f_j||_(X(I))
 +C*||f_i||_(L^infinity(I;H^(-p_*)))*product_(j!=i)||f_j||_(L^infinity(I;L^2)), i=1,2,3, (15)
||C_I(f_1,f_2,f_3)||_(L^2)<=C_alpha*|I|^alpha*product_j ||f_j||_(H^alpha),
0<=alpha<=1, f_j time-independent. (16)

## Page 7: (17)–(19)

There exists a_gamma in [0,1) such that
||fg||_(L^2)<=C_gamma*||f||_(H^gamma)*||g||_(H^(a_gamma)), (17)
and, with F_n(t;w)=(1/2)integral_(t_n)^t B_s(w,w) ds,
sup_(t_n<=t<=t_(n+1))||F_n(t;w)||_(H^(a_gamma))<=C_M*tau^gamma,
sup_(t_n<=t<=t_(n+1))||F_n(t;w)||_(H^(1+gamma))<=C_M, (18)
when ||w||_(H^gamma)<=M. The source text chooses a_gamma=1/2-gamma for 0<gamma<1/2, a_gamma=1/8 for gamma=1/2, and a_gamma=0 for gamma>1/2.
The source stage exponent is theta=(1+gamma-beta)/(1+gamma-beta_0), with beta_0=2*gamma-3/2 for 0<gamma<1/2, beta_0=-1/2-epsilon for gamma=1/2, beta_0=gamma-1 for 1/2<gamma<=1. The middle case fixes epsilon=1/8. At beta=a_gamma the exponents are (1/2+2*gamma)/(5/2-gamma)>=gamma, 11/17>1/2, and (1+gamma)/2>=gamma respectively; at beta=1+gamma the exponent is zero.
The original attributes (17)–(18) to [1, Lemma 7.2 and Eqs. (2.2)–(2.3)]; its L^2 and H^s norms are sqrt(2*pi) times those in the present paper.
The elementary bounds are
||partial_x^(-1)f||_(H^1)+||partial_x^(-1)f||_(L^infinity) \lesssim ||f||_(L^2),
||B_t(f,g)||_(H^(-p_*)) \lesssim ||f||_(L^2)*||g||_(L^2),
||J_t(f,g)||_(H^1) \lesssim ||f||_(L^2)*||g||_(L^2). (19)
In Section 4.2 the displayed coefficient estimate |\widehat{FG}(k)|<=||F||_2*||G||_2 has a Fourier hat over the whole product F*G, not just G. Its subsequent bound is
||B_t(f,g)||_(H^(-p_*))^2<=||f||_2^2*||g||_2^2*sum_(k!=0) k^2*<k>^(-2*p_*).
The text also states ||D^(-1)P(FG)||_2<=C||F||_2||G||_2,
||A||_(H^(-p_*))<=||D^(-1)A||_2 for mean-zero A, and
||J_t(A,B)||_2<=C||D^(-1)A||_2||B||_2.

## Pages 7–8: numerical interpolation and (20)–(21)

Initially the data are smooth. Let v^n=S_(-t_n)u^n, I_n=[t_n,t_(n+1)], f=v^n, w=v(t_n), delta_n=||f-w||_(L^2), q_n=tau^gamma+delta_n; assume delta_n<=1.
F_n(t)=(1/2)integral_(t_n)^t B_s(f,f) ds, z_n(t)=f+F_n(t),
C_n(t)=integral_(t_n)^t B_s(f,F_n(s)) ds,
Q_n(t)=(1/2)integral_(t_n)^t B_s(F_n(s),F_n(s)) ds,
W_n=Q_n(t_(n+1))+R^n_(2,tau)(f,f,f),
V(t)=f+F_n(t)+C_n(t)+Q_n(t)-((t-t_n)/tau)*W_n,
Y_n(t)=V(t)-z_n(t).
The original source identity is v^(n+1)=f+F_n(t_(n+1))+C_n(t_(n+1))-R^n_(2,tau)(f,f,f); source notation exp(t*partial_x^3) equals S_(-t), source A^n is C_n(t_(n+1)), source R_2^n is (4). Thus V(t_n)=v^n and V(t_(n+1))=v^(n+1).
F_n(t)=(1/6)[J_s(f,f)]_(s=t_n)^(s=t),
sup_(I_n)||F_n(t)||_(H^1)<=C_M,
sup_(I_n)||F_n(t)-F_n(t;w)||_(H^1)<=C_M*delta_n.
The numbered bounds are
sup_(I_n)||F_n(t)||_(H^(a_gamma))+sup_(I_n)||F_n(t)||_(L^2)<=C_M*q_n,
||z_n||_(X(I_n))<=C_M, (20)
sup_(I_n)||Q_n(t)||_(L^2)+||W_n||_(L^2)<=C_M*tau*q_n. (21)
The intervening displayed inequality is sup_(I_n)||B_t(F_n(t),F_n(t))||_(L^2)<=C_M*q_n, and the last page-8 display is
sup_(I_n)||partial_x^(-1)B_t(f,F_n(t))||_(L^2)<=C_M*q_n.

## Page 9: (22)–(28)

Y_n'=B_t(f,F_n)+(1/2)B_t(F_n,F_n)-tau^(-1)W_n,
sup_(I_n)||partial_x^(-1)Y_n||_(L^2)<=C_M*tau*q_n,
sup_(I_n)||partial_x^(-1)Y_n'||_(L^2)<=C_M*q_n. (22)
F_n'=(1/2)B_t(f,f), and
C_n(t)=(1/3)J_t(f,F_n(t))-(1/6)C_([t_n,t])(f,f,f).
sup_(I_n)||Y_n||_(L^2)<=C_M*q_n. (23)
||Y_n||_(X(I_n))<=C_M*q_n,
sup_(I_n)||Y_n||_(H^(-p_*))<=C_M*tau*q_n. (24)
The step residual is
rho_n(t)=-integral_(t_n)^t B_s(Y_n,z_n) ds
 -(1/2)integral_(t_n)^t B_s(Y_n,Y_n) ds-((t-t_n)/tau)*W_n.
Concatenate these increments into R(t), with R(0)=0. Then
V'=(1/2)B_t(V,V)+R',
R'=-B_t(Y_n,z_n)-(1/2)B_t(Y_n,Y_n)-tau^(-1)W_n. (25)
sup_(I_n)||rho_n||_(L^2)<=C_M*tau*q_n,
||R'||_(L^infinity(I_n;H^(-p_*)))<=C_M*q_n. (26)
For e=v-V, I=[a,b] starting at a grid point, h=b-a<=1, E_I=sup_I||e||_(L^2)<=1 (the final endpoint may lie inside a step),
sup_(a<=t<=b)||R(t)-R(a)||_(L^2)<=C_M*(h+tau)*(tau^gamma+E_I), (27)
||e||_(X(I))<=C_M*(tau^gamma+E_I),
||v||_(X(I))+||V||_(X(I))<=C_M. (28)

## Pages 10–11: (29)–(36)

F_I(t)=integral_a^t B_s(e,v-e/2) ds,
e(t)=e(a)+F_I(t)-(R(t)-R(a)). (29)
The proof-only Fourier threshold is N>=2; it is not part of the algorithm.
sup_(t in I)||P_(<=N)F_I(t)||_(L^2)<=C_M*N^2*h*E_I. (30)
F_I(t)=(1/3)[J_s(e,v-e/2)]_(s=a)^(s=t)
 -(1/3)C_([a,t])(e,v-e/2,V)-(1/6)C_([a,t])(v,v,e)
 +(1/3)integral_a^t J_s(R',V) ds. (31)
With g=v-e/2, the original text gives
e'=B(e,g)-R', g'=(1/2)B(v,v)-(1/2)B(e,g)+(1/2)R',
C(e,g,g)-(1/2)C(e,g,e)=C(e,g,V), g-e/2=V,
-J(R',g)+(1/2)J(e,R')=-J(R',V).
For the proof-only projections L=P_(<=N/3), H=I-L,
C(f_1,f_2,f_3)-C(Lf_1,Lf_2,Lf_3)
 =C(Hf_1,f_2,f_3)+C(Lf_1,Hf_2,f_3)+C(Lf_1,Lf_2,Hf_3),
||Hf_i||_(H^(-p_*))<=C*N^(-p_*)||f_i||_2.
||P_(>N)C_I(f_1,f_2,f_3)||_(L^2)
 <=C*h*product_j ||f_j||_(X(I))+C*N^(-p_*)*product_j||f_j||_(L^infinity(I;L^2)). (32)
The displayed terms from the forcing integral on each intersected step are
-C(Y_n,z_n,V), -(1/2)C(Y_n,Y_n,V), -tau^(-1)integral J_s(W_n,V) ds.
sup_(t in I)||P_(>N)F_I(t)||_(L^2)
 <=C_M*(h+tau)*tau^gamma+C_M*(h+tau+N^(-1)+N^(-p_*))*E_I. (33)
E_I<=||e(a)||_(L^2)+C_M*(h+tau)*tau^gamma
 +C_M*(N^2*h+h+tau+N^(-1)+N^(-p_*))*E_I. (34)
The text fixes N with C_M*(N^(-1)+N^(-p_*))<=1/4, then delta in (0,1] with C_M*delta*(N^2+3)<=1/4, and restricts tau<=delta/2. For intervals starting at grid points of length at most delta,
E_I<=2||e(a)||_(L^2)+C_M'*delta*tau^gamma. (35)
Page 11 uses blocks of floor(delta/tau) steps, lengths in [delta/2,delta], possibly a shorter final block, with number at most 2*T/delta+1. Starting from e(0)=0, the stated bound is
sup_(0<=t<=T)||e(t)||_(L^2)<=C_(M,gamma,T)*tau^gamma. (36)
The following original paragraph gives the continuous bootstrap contradiction and the fixed-timestep density passage, with u_(0,m)=P_(<=m)u_0, ||u_(0,m)||_(H^gamma)<=R,
sup_([0,T])||u_m-u||_2<=C(T,2R)||u_(0,m)-u_0||_2 -> 0,
and continuity of every term in the unmodified update on L^2 for each fixed tau>0. It ends with S_(t_n) unitary and V(t_n)=S_(-t_n)u^n, identifying the grid error with ||u(t_n)-u^n||_(L^2).

The numerical-data reality convention on page 11 reads b_(-k)=overline(b_k), b_0=0; the conjugation bar is also lost by plain extraction. This is a transcription detail of the experiment, not an added theorem hypothesis.
