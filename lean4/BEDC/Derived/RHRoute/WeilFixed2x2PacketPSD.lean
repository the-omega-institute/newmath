import BEDC.Derived.RHRoute.IntervalMatrixPSD

/-
Fixed 2×2 Weil-Gram PSD certificate consumer (oracle-scoped ownable fragment of #1).

Toward making `WeilGramRoute.AllFiniteWeilGramPSD` (= ∀ ruler, PSD ...) constructible:
the `∀`-over-all-rulers IS the RH wall, so this owns only the honest fragment the
adversarial consensus endorsed — a consumer that turns a certified interval packet for
ONE fixed 2×2 ruler into a genuine PSD proof, reusing (not rebuilding) the existing
`IntervalMatrixPSD.psd_2x2_interval` checker.

Honest boundary (explicit):
  * proves: one concrete certified 2×2 (symmetric, real-diagonal-nonneg, interval-
    determinant-dominant) matrix is PSD for all coefficients;
  * does NOT prove: `AllFiniteWeilGramPSD`, `GlobalWeilPositivity`, or RH (the ∀-ruler
    wall);
  * does NOT prove: that the certified rational intervals enclose the TRUE completed-ζ
    archimedean Γ entries — that is `ArchimedeanEntryObligation`, Loning's territory, and
    is exactly the interface this consumer waits on (`Fixed2x2Cert` is what a certified
    arch/prime entry packet would inhabit).
All 0-axiom; the numeric facts are cert INPUTS, so no located-ζ content leaks in.
-/

namespace BEDC.Derived.RHRoute.WeilFixed2x2PacketPSD

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.IntervalMatrixPSD

abbrev Rat : Type := RatNum

/-- A certified fixed 2×2 symmetric interval packet: rational interval bounds for the
three entries, the ordering / diagonal-nonneg / interval-determinant-dominance facts
required by `psd_2x2_interval`, and concrete entry values inside the intervals. This is
the object a certified Weil-Gram entry packet (prime term + Loning's archimedean entry
bounds) would inhabit. -/
structure Fixed2x2Cert where
  lo11 : Rat
  hi11 : Rat
  lo12 : Rat
  hi12 : Rat
  lo22 : Rat
  hi22 : Rat
  b11 : Rat
  b12 : Rat
  b22 : Rat
  hord11 : ratLe lo11 hi11
  hord12 : ratLe lo12 hi12
  hord22 : ratLe lo22 hi22
  hlo11Nonneg : ratLe ratZero lo11
  hlo22Nonneg : ratLe ratZero lo22
  hdetCert :
    ratLe (ratMul (offdiagAbsBound lo12 hi12) (offdiagAbsBound lo12 hi12))
      (ratMul lo11 lo22)
  hb11lo : ratLe lo11 b11
  hb11hi : ratLe b11 hi11
  hb12lo : ratLe lo12 b12
  hb12hi : ratLe b12 hi12
  hb22lo : ratLe lo22 b22
  hb22hi : ratLe b22 hi22

/-- The consumer: a `Fixed2x2Cert` yields the 2×2 Gram quadratic form nonneg for ALL
coefficients `c1 c2` — the fixed-ruler PSD body. Reuses the existing checker; 0-axiom. -/
theorem fixed2x2_cert_psd (C : Fixed2x2Cert) (c1 c2 : Rat) :
    ratLe ratZero
      (ratAdd
        (ratAdd
          (ratMul C.b11 (ratMul c1 c1))
          (ratMul (ratMul (natRat 2) C.b12) (ratMul c1 c2)))
        (ratMul C.b22 (ratMul c2 c2))) :=
  psd_2x2_interval
    C.lo11 C.hi11 C.lo12 C.hi12 C.lo22 C.hi22
    C.hord11 C.hord12 C.hord22
    C.hlo11Nonneg C.hlo22Nonneg C.hdetCert
    C.b11 C.b12 C.b22
    C.hb11lo C.hb11hi C.hb12lo C.hb12hi C.hb22lo C.hb22hi
    c1 c2

end BEDC.Derived.RHRoute.WeilFixed2x2PacketPSD
