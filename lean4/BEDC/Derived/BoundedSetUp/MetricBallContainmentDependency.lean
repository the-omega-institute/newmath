import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_metric_ball_containment_dependency [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      containmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead transport containmentRead ->
            PkgSig bundle containmentRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row containmentRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
                      hsame row ball ∨ hsame row ballRead ∨ hsame row containmentRead ∨
                        Cont S center memberRead ∨ Cont memberRead radius ballRead ∨
                          Cont ballRead transport containmentRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
                      PkgSig bundle containmentRead pkg ∧ hsame row containmentRead)
                  hsame ∧
                UnaryHistory memberRead ∧ UnaryHistory ballRead ∧
                  UnaryHistory containmentRead ∧ Cont S center memberRead ∧
                    Cont memberRead radius ballRead ∧
                      Cont ballRead transport containmentRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier subsetCenter memberRadius ballTransportContainment containmentPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have containmentUnary : UnaryHistory containmentRead :=
    unary_cont_closed ballReadUnary transportUnary ballTransportContainment
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row containmentRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
              hsame row ball ∨ hsame row ballRead ∨ hsame row containmentRead ∨
                Cont S center memberRead ∨ Cont memberRead radius ballRead ∨
                  Cont ballRead transport containmentRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
              PkgSig bundle containmentRead pkg ∧ hsame row containmentRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro containmentRead
        ⟨hsame_refl containmentRead, containmentUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, namePkg, containmentPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, containmentUnary, subsetCenter, memberRadius,
      ballTransportContainment⟩

end BEDC.Derived.BoundedSetUp
