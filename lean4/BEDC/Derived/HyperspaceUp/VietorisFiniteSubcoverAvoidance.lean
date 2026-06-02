import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisFiniteSubcoverAvoidance [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M hitRead missRead coverRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ->
      Cont K0 N0 hitRead ->
        Cont K1 N1 missRead ->
          Cont hitRead missRead coverRead ->
            Cont Hs C replayRead ->
              PkgSig bundle coverRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row coverRead \/ hsame row replayRead) /\ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X \/ hsame row K0 \/ hsame row K1 \/ hsame row N0 \/
                        hsame row N1 \/ hsame row D0 \/ hsame row D1 \/ hsame row R \/
                          hsame row Hs \/ hsame row C \/ hsame row P \/ hsame row M \/
                            hsame row hitRead \/ hsame row missRead \/
                              hsame row coverRead \/ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row /\ PkgSig bundle P pkg /\ PkgSig bundle coverRead pkg)
                    hsame /\
                  UnaryHistory hitRead /\ UnaryHistory missRead /\ UnaryHistory coverRead /\
                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle Pkg SemanticNameCert
  intro carrier hitRoute missRoute coverRoute replayRoute coverPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    _rUnary, hsUnary, cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have hitUnary : UnaryHistory hitRead :=
    unary_cont_closed k0Unary n0Unary hitRoute
  have missUnary : UnaryHistory missRead :=
    unary_cont_closed k1Unary n1Unary missRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed hitUnary missUnary coverRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row coverRead \/ hsame row replayRead) /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row X \/ hsame row K0 \/ hsame row K1 \/ hsame row N0 \/
              hsame row N1 \/ hsame row D0 \/ hsame row D1 \/ hsame row R \/
                hsame row Hs \/ hsame row C \/ hsame row P \/ hsame row M \/
                  hsame row hitRead \/ hsame row missRead \/ hsame row coverRead \/
                    hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row /\ PkgSig bundle P pkg /\ PkgSig bundle coverRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro coverRead ⟨Or.inl (hsame_refl coverRead), coverUnary⟩
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
        constructor
        · cases source.left with
          | inl coverSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) coverSame)
          | inr replaySame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) replaySame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl coverSame =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          left
          exact coverSame
      | inr replaySame =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact replaySame
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, coverPkg⟩
  }
  exact ⟨cert, hitUnary, missUnary, coverUnary, replayUnary⟩

end BEDC.Derived.HyperspaceUp
