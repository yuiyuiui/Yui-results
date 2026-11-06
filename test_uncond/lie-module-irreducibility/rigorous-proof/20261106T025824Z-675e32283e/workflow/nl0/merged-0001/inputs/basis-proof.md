The selected full target and the original hypotheses H are unchanged. In particular p is any prime; K is any field of characteristic p, without an algebraic-closure assumption; lambda is an integer with 0≤lambda<p; V(lambda) is the given complex irreducible highest-weight sl2 module of dimension lambda+1; x,y,h and the nonzero highest-weight vector v have the stated normalization; and M is an arbitrary admissible lattice stable under every original divided power. Irreducibility of the complex module is retained as an original hypothesis, though the following argument only needs its stated dimension and highest-weight data. No new assumption on M is introduced.

We use ell=lambda.toNat, so the original inequality 0≤lambda gives lambda=(ell:Z), and the range becomes ell<p. All coefficients ell−2i in complex or integer formulas mean integer subtraction, even when negative. Index sets {0,...,ell} mean Fin(ell+1); factorials and binomial coefficients are those of natural numbers. Endomorphism products act on the rightmost argument first. Write X_r=(r!)^(-1)x^r and Y_r=(r!)^(-1)y^r exactly as in the problem; the definitions dividedPower and Stable are recorded in lean_header. The header's AdmissibleLattice packages a choice of the original common integer/complex basis indexed by Fin n. This packaging is justified below by B007, rather than assumed for a special lattice.

The native foundational propositions are B001 (independent families of the correct finite size span), B002 (a free integer basis extends to a field basis), B003 (factorials of indices below p have nonzero image), B004 (the binomial/factorial identity), B006 (basis expansion and determination of endomorphisms), and B007 (finiteness and cardinality of any basis in finite dimension). B005 is the prepared closed compatibility adapter for scalar extension of endomorphisms as a ring homomorphism. Their actual closed Lean proofs accompany the registry. We now give the recursive internal derivations; these class-3 facts are to be proved internally in the later NL0/Lean work, not supplied as external premises.

B101: characteristic-zero coordinates, including termination.

For every i≥0, the relations hy=yh−2y and xy=yx+h give
  h y^i v=(ell−2i)y^i v,
  x y^(i+1)v=(i+1)(ell−i)y^i v.
The first identity follows by induction from hv=ell v. For the second, the base i=0 is xyv=yxv+hv=ell v. If xy^i v=i(ell−i+1)y^(i−1)v, then
  xy^(i+1)v=y(xy^i v)+hy^i v
            =[i(ell−i+1)+(ell−2i)]y^i v
            =(i+1)(ell−i)y^i v.
Thus this induction does not use any termination assertion.

For 0≤i≤ell, applying x repeatedly gives
  x^i y^i v=[product_(r=1,...,i) r(ell−r+1)]v.
Every factor is a positive integer if i>0 and hence is nonzero in C; for i=0 the product is 1. Since v≠0, y^i v≠0. Define e_i=y^i v/i!, which is also nonzero. The eigenvalues a_i=ell−2i are pairwise distinct in C: equality would imply 2(i−j)=0 in characteristic zero and hence i=j.

To prove independence, take a relation sum_i z_i e_i=0 and fix j. Apply the composition product_(k≠j)(h−a_k Id). Each e_i with i≠j is killed by the factor k=i. The surviving term is
  z_j [product_(k≠j)(a_j−a_k)] e_j=0.
Every scalar factor and e_j is nonzero, so z_j=0. This works for every j and includes the singleton index set. By B001 the ell+1 vectors span V of dimension ell+1, and independence together with spanning defines a basis.

The first recurrence also makes z=y^(ell+1)v an h-eigenvector with eigenvalue a=−ell−2 (the vector z is permitted to be zero). Expand z in this basis using B006. Applying h−a Id gives
  sum_i z_i(a_i−a)e_i=0.
For i≤ell, a_i−a=2(ell+1−i)≠0 in C. Independence gives every z_i=0, so z=0. All higher lowering powers vanish as well. Dividing the recurrences by i!, and using (i+1)!=(i+1)i!, now gives exactly
  xe_0=0; xe_i=(ell−i+1)e_(i−1) for 1≤i≤ell;
  ye_i=(i+1)e_(i+1) for i<ell; ye_ell=0;
  he_i=(ell−2i)e_i.
For r≤i, iterating x gives the coefficient product_(s=1,...,r)(ell−i+s) on e_(i−r). Division by r! gives choose(ell−i+r,r), by B004 with n=ell−i+r and j=r and cancellation of the nonzero factorial (ell−i)!. If r>i, the lowering in index reaches e_0 and is then killed by x. For i+r≤ell, iterating y gives (i+r)!/i! on e_(i+r); division by r! gives choose(i+r,r) by B004. If i+r>ell, the string reaches e_ell and is killed by y. These are precisely the divided-power formulas for all r, including r=0. This proves B101 from B001, B004, and B006.

B102: integral scaled matrix units on the arbitrary lattice.

Admissibility says that every X_r and Y_r carries M into M. Their restrictions X_r^M,Y_r^M are Z-linear endomorphisms. The inclusion M→V is injective, since M is an actual subgroup; it intertwines each restricted operator with the corresponding complex operator. In particular x_M=X_1^M and y_M=Y_1^M are the original x,y restricted to M. Since h=xy−yx, h also restricts and equals x_M y_M−y_M x_M. For each r≥0 the defining complex identity r! X_r=x^r, and injectivity of M→V, give the integer endomorphism identity r! X_r^M=x_M^r, and likewise for Y_r^M and y_M. Here integer multiples are repeated addition of endomorphisms, not division in M.

Use the B101 basis to define E_ij in End_C(V) by E_ij e_k=e_i if k=j and zero otherwise. Define
  P=Y_ell X_ell,    c_j=choose(ell,j),
  A_ij^C=X_(ell−i) P Y_(ell−j).
The divided-power formulas give P=E_(ell,ell): X_ell kills each e_k with k<ell, while it sends e_ell to e_0, and Y_ell sends e_0 to e_ell. They also give X_(ell−i) P=E_(i,ell), since X_(ell−i)e_ell=e_i.

For P Y_(ell−j), examine an input e_k. If k<j, its image under Y_(ell−j) has index below ell and is killed by P. If k>j it is sent beyond the end and is zero already. If k=j its image is choose(ell,ell−j)e_ell=c_j e_ell. The equality of the two binomial coefficients follows from B004 for j and ell−j by cancellation of the equal nonzero factorial products in the integers. Consequently
  P Y_(ell−j)=c_j E_(ell,j),   A_ij^C=c_j E_ij.
Each equality is established on all basis vectors and hence is an endomorphism equality by B006.

The same product of restricted divided powers defines
  P_M=Y_ell^M X_ell^M,   A_ij=X_(ell−i)^M P_M Y_(ell−j)^M
in End_Z(M). Thus the restriction of A_ij^C is A_ij; no assertion that E_ij itself preserves M over Z is being made.

The coordinate matrix units obey E_ij E_kl=E_il if j=k and zero otherwise. Multiplying the scaled formulas therefore gives
  A_ij^C A_kl^C=c_j A_il^C if j=k, and zero otherwise.
Indeed, when j=k, the left side is c_j c_l E_il and A_il^C=c_l E_il. Put
  D=product_(j=0,...,ell)c_j,
  d_j=product_(k=0,...,ell; k≠j)c_k.
Then d_j c_j=D, including the singleton case. On each e_k one has
  (sum_j d_j A_jj^C)e_k=D e_k,
so B006 gives sum_j d_j A_jj^C=D Id_V. All coefficients are integers and all operators in these identities preserve M. Composing with the injective inclusion of M into V proves in End_Z(M) that
  A_ij A_kl= c_j A_il if j=k, and zero otherwise,
  sum_j d_j A_jj=D Id_M.
This proves B102. It uses no localization, rationality of lattice coordinates, fractional ideals, or classification of modules over a discrete valuation ring.

B104: match the original tensor product and compute its dimension.

The given Z-basis of M, after inclusion into V, is a complex basis. Apply B007 to that complex basis: its index type is finite and has cardinality dim_C V=ell+1. Choose a bijection with Fin(ell+1) and reindex both the Z-basis and the complex basis by the same bijection. Their inclusion relation is unchanged. This is exactly the header's AdmissibleLattice with n=ell+1, and works for every original admissible lattice.

Let U=K⊗_Z M. By B002, U has a K-basis q_i=1⊗m_i indexed by Fin(ell+1), and dim_K U=ell+1. It is nonzero: q_0 cannot be zero, since its basis coordinate at 0 is 1 and 1≠0 in K. This supplies nonzeroness without assuming that M has a special basis related to the e_i.

For completeness define S:M⊗_Z K→K⊗_Z M by
  S(m⊗a)=a⊗m,
and S_inv in the other direction by S_inv(a⊗m)=m⊗a. Both displayed rules are additive in each variable and balanced over Z, because moving an integer scalar between the tensor factors has the same effect on either side. The defining universal property of the tensor product therefore gives additive maps. Give M⊗_Z K its usual K-action on the second factor and U its K-action on the first factor. For b∈K,
  S(b·(m⊗a))=S(m⊗ba)=ba⊗m=b·S(m⊗a);
the same calculation proves K-linearity of S_inv. Their composites fix every pure tensor, and every tensor is a finite sum of pure tensors, so they are mutual inverses. This is a concrete K-linear isomorphism, rather than an additional tensor-associativity premise.

For f∈End_Z(M), its original induced operator f_K on M⊗K is defined on pure tensors by f_K(m⊗a)=f(m)⊗a. The same balanced-bilinear verification makes this well-defined and K-linear. B005 gives F(f)(a⊗m)=a⊗f(m), hence
  S(f_K(m⊗a))=a⊗f(m)=F(f)(S(m⊗a)).
Again equality on pure tensors gives S f_K=F(f) S everywhere. In particular this applies to x_M,y_M,h_M and every divided power. Thus invariant subspaces and the zero and whole spaces correspond under S, and the original tensor product is nonzero. This proves B104 from B002, B005, and B007.

B103: reduction and normalized matrix units; invariant subspaces remain stable.

Apply B005 to M and K and write F for its unital ring homomorphism. A bar on a natural or integer coefficient means its image in K. B003 gives overline(ell!)≠0, because ell<p. For 0≤j≤ell, B004 gives in K
  cbar_j · overline(j!) · overline((ell−j)!)=overline(ell!)≠0.
A product equal to a nonzero element of a field has no zero factor, so cbar_j≠0. Thus Dbar=product_j cbar_j≠0. Define
  T_ij=(cbar_j)^(-1) F(A_ij) ∈ End_K(U).
The ring homomorphism F preserves finite sums, products, the identity, and integer multiples. For clarity integer multiples can be expressed by repeated addition and negation of the identity and multiplication; preservation follows from the RingHom laws. In End_K(U), integer multiplication of an endomorphism is the same as scalar multiplication by its image in K.

Apply F to the multiplication identities of B102. If j≠k then T_ij T_kl=0. If j=k then
  T_ij T_kl
   =(cbar_j)^(-1)(cbar_l)^(-1) F(c_j A_il)
   =(cbar_l)^(-1) F(A_il)=T_il.
All scalar inverses used here exist by the preceding nonvanishing. Apply F to the sum identity:
  sum_j dbar_j F(A_jj)=Dbar Id_U.
Since dbar_j cbar_j=Dbar and both cbar_j and Dbar are nonzero, division by Dbar gives
  sum_j T_jj=Id_U.
Thus these are actual matrix-unit relations on U; their construction and proof do not need a coordinate identification of the reduced arbitrary lattice with the characteristic-zero e_i.

Now let W be a K-subspace of U invariant under x'=F(x_M) and y'=F(y_M). Induction on r shows that it is invariant under (x')^r and (y')^r, including the identity at r=0. For every 0≤r≤ell, B003 gives overline(r!)≠0. Applying F to the B102 factorial identities, and using preservation of powers, yields
  F(X_r^M)=overline(r!)^(-1)(x')^r,
  F(Y_r^M)=overline(r!)^(-1)(y')^r.
Because W is K-linear, it is invariant under these scalar multiples. Each A_ij uses only indices ell−i,ell,ell−j between 0 and ell, so its image under F is a composition of operators preserving W. Finally scalar multiplication by cbar_j^(-1) also preserves W, proving that all T_ij preserve W. This proves B103 from B003, B004, B005, and B102. It does not infer stability of divided powers from Lie invariance for any index at or above p.

B105: the finite matrix-unit irreducibility argument.

Let K be any field, n>0, dim_K U=n, and let endomorphisms T_ij, indexed by Fin n, have the displayed multiplication and diagonal-sum relations. Suppose W is stable under them and W≠0. Choose w∈W with w≠0. Since w=sum_j T_jj w, there exists j with u=T_jj w≠0. Stability gives u∈W, and the relation T_jj^2=T_jj gives T_jj u=u.

For each i set u_i=T_ij u. These n vectors belong to W. If sum_i a_i u_i=0, fix k and apply T_jk. The multiplication relation gives
  0=sum_i a_i T_jk T_ij u=a_k T_jj u=a_k u.
Since u≠0 and K is a field, a_k=0. Every k has zero coefficient, so the family (u_i) is linearly independent. Its index cardinality n equals dim_K U; B001 therefore gives span_K{u_i}=U. As W contains every u_i, it contains their span and equals U. Together with the alternative W=0, this proves B105. This argument is valid even when the image of n in K is zero; it never divides by n or takes traces.

B106: the complete original target.

Take the original arbitrary admissible lattice, prime p, field K, and integer lambda, and use ell as at the start. B104 gives a nonzero U=K⊗_Z M of dimension ell+1 and an intertwining K-linear isomorphism S from the originally specified V(K)=M⊗_Z K. The induced x,y,h operators are precisely those in the problem: h restricts by [x,y]=h, and scalar extension of their integral restrictions preserves all three given Chevalley commutator relations. In particular this is still the stipulated Chevalley action in characteristic 2; no alternative definition using a quotient by a scalar element or a characteristic-dependent identification is used. The construction of the Lie algebra tensor and its action is just Z-bilinear extension of these operators, so invariance under its generators is the stipulated x,y,h invariance.

Let W be any K-linear subspace of V(K) invariant under x,y,h. Its image S(W) is K-linear and invariant under x'=F(x_M) and y'=F(y_M), by the intertwining identities. B103 supplies endomorphisms T_ij satisfying the matrix-unit relations and preserving S(W). Apply B105 with n=ell+1>0. It gives S(W)=0 or S(W)=U; applying the inverse isomorphism gives W=0 or W=V(K). B104 already proves V(K)≠0. This proves every clause of the full target.

If lambda=0, the sole index is 0, X_0=Y_0=Id, c_0=D=d_0=1, and the same construction and proof apply. If p=2, ell is 0 or 1, and all factorials actually inverted have index below 2; the argument never asks for distinct h-eigenvalues in K. All eigenvalue separation occurred only in the original characteristic-zero space. No algebraic closure of K, choice of a minimal lattice, or additional hypothesis on p is used.

Replacement accounting. The original localized-lattice route is replaced, not retained as an unproved premise. Its injection and rank facts for Z_(p)⊗M, coordinate modules J_i, equality of all J_i, dimension computation for Q⊗J, injectivity of its multiplication map, and principal fractional-ideal/valuation argument are unnecessary because B102 gives integer polynomial endomorphism identities and B103 reduces them directly. The original scalar-extension/localization and residue-field tensor isomorphisms are replaced by B104's explicit tensor swap and B002's direct basis extension. The original invariant-subspace argument requiring a common scaled e_i lattice basis is replaced by B105's dimension argument for abstract matrix units. These changes preserve the original target and every allowed H while eliminating all localization and discrete-valuation dependencies. The actual remaining foundational uses are the prepared 1/adapted-1 proofs and the concrete internal derivations above; there are no unresolved class-4 dependencies.