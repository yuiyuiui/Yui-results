A sphere-valued map cannot vanish outside a compact set. As approved by
the user on 2026-10-23, interpret spatial compact support as compact support
of a perturbation from a **fixed unit vector**, locally uniformly in time.
This is a disclosed nontrivial interpretation, not a claimed author-issued
correction.

Let \(n,m\geq1\) be integers and let
\(u:\mathbb R^n\times(0,\infty)\to\mathbb R^m\) be jointly smooth.
Fix \(q\in\mathbb R^m\) with \(|q|=1\). Assume:

1. \(|u(x,t)|=1\) for all \(x\) and \(t>0\).
2. The acceleration \(u_{tt}-\Delta_xu\) is normal to the sphere at
   \(u\): at each point there is a real scalar \(a(x,t)\) with
   \(u_{tt}-\Delta_xu=a u\). No regularity of the selected scalar is
   assumed.
3. For every \(0<s<t<\infty\), a compact set
   \(C_{[s,t]}\subset\mathbb R^n\) exists such that \(u(x,r)=q\) for
   \(x\notin C_{[s,t]}\), \(r\in[s,t]\).

With Euclidean norms and Lebesgue measure, define

\[
e(x,t)=|u_t(x,t)|^2+\sum_{j=1}^n|\partial_{x_j}u(x,t)|^2,
\qquad E(t)=\int_{\mathbb R^n}e(x,t)\,dx.
\]

The spatial gradient square is the Frobenius square, and
\(\Delta_xu=\sum_j\partial_{x_jx_j}u\) component by component.
Prove integrability of \(e(\cdot,t)\), differentiability of \(E\),
and \(E'(t)=0\) for every \(t>0\). No assertion at time zero is required.
