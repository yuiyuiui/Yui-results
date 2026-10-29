Primary-source recheck at final correspondence stage

Babin–Ilyin–Titi, arXiv:0910.1389v2 (23 October 2010), accessed through the primary arXiv PDF.

- Equation (4.1), PDF page 11, initializes all nonzero Fourier modes with the full initial datum. Modes outside the projection are stationary; this is stated immediately after (4.2). Thus SourceGalerkinODE is the original full-tail system, not a substituted zero-tail Galerkin system.
- Theorem 4.2, PDF page 13, gives the estimate uniform in the projection with the constant depending on the actual initial homogeneous norm. The formal fixed-sphere premise retains this dependence. Initial-ball uniformity is derived internally.
- Theorem 4.3, PDF page 14, fixes sigma before the subsequence, retains strong finite-p convergence and weak-star top-space convergence, and gives an almost-everywhere energy identity.
- Theorem 5.1, PDF page 19, concerns the constructed limiting solution, Sobolev continuity, uniqueness, dependence through (5.18), and all-time energy. The proof preceding (5.18), PDF page 21, uses close initial points and iterates the local dependence bound. The formal SourceLocalLipschitz field records the qualitative local solution-map conclusion; the convergence argument uses the separately encoded full weaker-norm estimate (6.22) at theta zero.
- Theorem 6.3, PDF page 27, concerns the same constructed limit in the range 0<s<=1/2 and dependence through (6.7).

This is a manual verification record. It is not independent certification of the Lean-to-primary-source translation.
