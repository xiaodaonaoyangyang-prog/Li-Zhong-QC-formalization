import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

/-!
# Hubbard 2006, Chapter 7 §7.1: Finite-dimensional Teichmüller spaces

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3768–3802.

**Conventions.** Hubbard's `T_X` is modelled by the project's finite-type Teichmüller spaces
`LiZhongQC.TeichSpaceFiniteType S₀ g n m` (for a surface without ideal boundary, `m = 0`); Hubbard's `T_S` with ideal
boundary (`rel I(S)`, Def. 6.4.1) is not modelled. The only item of this section is Proposition 7.1.1; its two halves
differ in status.

* Proposition 7.1.1 (⇐: a surface of genus `g` with `n` points removed has a Teichmüller space of real dimension `6g − 6
  + 2n`, complex dimension `3g − 3 + n`) — exists: `LiZhongQC.teichSpaceFiniteType_ball` (the first conjunct is the
  dimension 6g − 6 + 2n + 3m of the space of admissible quadratic differentials, m = 0; the second is the bijection
  of the unit ball with T_{g,n,m}; the complex dimension is half of the real one)
* Proposition 7.1.1 (⇒: if the Teichmüller space is finite dimensional, then X is of finite type) — deferred: needs the
  Teichmüller space of an infinite-type surface (infinite multicurves and the ideal boundary I(X), Ch. 6.4 with rel I)
  and a notion of the dimension of the Teichmüller space; none is in the project
* Example 7.1.2 (homeomorphic Riemann surfaces in different Teichmüller spaces) — omitted: example (not cited)
-/

namespace Hubbard2006

end Hubbard2006
