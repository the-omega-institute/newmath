import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicUpRealRegSeqRatCommonWindowReadback [AskSetup] [PackageSetup]
    {Q0 S0 R0 E0 H0 C0 P0 N0 Q1 S1 R1 E1 H1 C1 P1 N1 commonWindow readback0
      readback1 seal0 seal1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier Q0 S0 R0 E0 H0 C0 P0 N0 bundle pkg ->
      DyadicCarrier Q1 S1 R1 E1 H1 C1 P1 N1 bundle pkg ->
        Cont S0 S1 commonWindow ->
          Cont commonWindow R0 readback0 ->
            Cont commonWindow R1 readback1 ->
              Cont readback0 E0 seal0 ->
                Cont readback1 E1 seal1 ->
                  PkgSig bundle seal0 pkg ->
                    PkgSig bundle seal1 pkg ->
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row readback0 ∨ hsame row readback1 ∨
                              hsame row seal0 ∨ hsame row seal1) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q0 ∨ hsame row Q1 ∨ hsame row commonWindow ∨
                              hsame row readback0 ∨ hsame row readback1 ∨
                                hsame row seal0 ∨ hsame row seal1)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S0 S1 commonWindow ∧
                              Cont commonWindow R0 readback0 ∧
                                Cont commonWindow R1 readback1 ∧
                                  Cont readback0 E0 seal0 ∧ Cont readback1 E1 seal1)
                          hsame ∧
                        UnaryHistory commonWindow ∧ UnaryHistory readback0 ∧
                          UnaryHistory readback1 := by
  -- BEDC touchpoint anchor: DyadicCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier0 carrier1 commonRoute readback0Route readback1Route seal0Route seal1Route
    _seal0Pkg _seal1Pkg
  obtain ⟨_q0Unary, s0Unary, r0Unary, e0Unary, _h0Unary, _c0Unary, _p0Unary,
    _n0Unary, _qsr0Route, _rec0Route, _p0Pkg, _n0Pkg⟩ := carrier0
  obtain ⟨_q1Unary, s1Unary, r1Unary, e1Unary, _h1Unary, _c1Unary, _p1Unary,
    _n1Unary, _qsr1Route, _rec1Route, _p1Pkg, _n1Pkg⟩ := carrier1
  have commonUnary : UnaryHistory commonWindow :=
    unary_cont_closed s0Unary s1Unary commonRoute
  have readback0Unary : UnaryHistory readback0 :=
    unary_cont_closed commonUnary r0Unary readback0Route
  have readback1Unary : UnaryHistory readback1 :=
    unary_cont_closed commonUnary r1Unary readback1Route
  have seal0Unary : UnaryHistory seal0 :=
    unary_cont_closed readback0Unary e0Unary seal0Route
  have seal1Unary : UnaryHistory seal1 :=
    unary_cont_closed readback1Unary e1Unary seal1Route
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row readback0 ∨ hsame row readback1 ∨ hsame row seal0 ∨
              hsame row seal1) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q0 ∨ hsame row Q1 ∨ hsame row commonWindow ∨
              hsame row readback0 ∨ hsame row readback1 ∨ hsame row seal0 ∨
                hsame row seal1)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S0 S1 commonWindow ∧
              Cont commonWindow R0 readback0 ∧ Cont commonWindow R1 readback1 ∧
                Cont readback0 E0 seal0 ∧ Cont readback1 E1 seal1)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro readback0 ⟨Or.inl (hsame_refl readback0), readback0Unary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameReadback0 =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameReadback0)))
      | inr rest =>
          cases rest with
          | inl sameReadback1 =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameReadback1))))
          | inr rest =>
              cases rest with
              | inl sameSeal0 =>
                  exact Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSeal0)))))
              | inr sameSeal1 =>
                  exact Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSeal1)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, commonRoute, readback0Route, readback1Route, seal0Route,
          seal1Route⟩
  }
  exact ⟨cert, commonUnary, readback0Unary, readback1Unary⟩

end BEDC.Derived.DyadicUp
