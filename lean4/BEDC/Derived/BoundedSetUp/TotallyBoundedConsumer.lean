import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_totally_bounded_consumer [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow finiteNet netRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S ball finiteNet ->
        Cont finiteNet replay netRead ->
          Cont netRead nameRow consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row ball ∨ hsame row finiteNet ∨
                      Cont netRead nameRow consumerRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                      hsame row consumerRead)
                  hsame ∧
                UnaryHistory finiteNet ∧ UnaryHistory netRead ∧
                  UnaryHistory consumerRead ∧ Cont S ball finiteNet ∧
                    Cont finiteNet replay netRead ∧ Cont netRead nameRow consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier finiteNetRoute netReadRoute consumerRoute consumerPkg
  obtain ⟨_xUnary, sUnary, _centerUnary, _radiusUnary, ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have finiteNetUnary : UnaryHistory finiteNet :=
    unary_cont_closed sUnary ballUnary finiteNetRoute
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed finiteNetUnary replayUnary netReadRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed netReadUnary nameUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ball ∨ hsame row finiteNet ∨ Cont netRead nameRow consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact Or.inr (Or.inr consumerRoute)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, finiteNetUnary, netReadUnary, consumerUnary, finiteNetRoute, netReadRoute,
      consumerRoute⟩

end BEDC.Derived.BoundedSetUp
