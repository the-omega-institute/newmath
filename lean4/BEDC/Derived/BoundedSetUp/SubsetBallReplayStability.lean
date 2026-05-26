import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_subset_ball_replay_stability [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead transport stableRead ->
            PkgSig bundle stableRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
                      hsame row ballRead ∨ Cont ballRead transport stableRead)
                  (fun row : BHist => PkgSig bundle stableRead pkg ∧ hsame row stableRead)
                  hsame ∧
                UnaryHistory memberRead ∧ UnaryHistory ballRead ∧ UnaryHistory stableRead ∧
                  Cont S center memberRead ∧ Cont memberRead radius ballRead ∧
                    Cont ballRead transport stableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier subsetCenter memberRadius ballTransport stablePkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    _provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed ballReadUnary transportUnary ballTransport
  have sourceStable :
      (fun row : BHist => hsame row stableRead ∧ UnaryHistory row) stableRead := by
    exact ⟨hsame_refl stableRead, stableUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
              hsame row ballRead ∨ Cont ballRead transport stableRead)
          (fun row : BHist => PkgSig bundle stableRead pkg ∧ hsame row stableRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stableRead sourceStable
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ballTransport))))
    ledger_sound := by
      intro _row source
      exact ⟨stablePkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, stableUnary, subsetCenter, memberRadius,
      ballTransport⟩

end BEDC.Derived.BoundedSetUp
