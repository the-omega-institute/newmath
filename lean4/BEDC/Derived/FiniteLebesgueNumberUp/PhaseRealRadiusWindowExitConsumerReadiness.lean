import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealRadiusWindowExitConsumerReadiness
    [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead
      realSealRead supportRead replayRead compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh dyadicRead ->
        Cont dyadicRead window streamRead ->
          Cont streamRead route realSealRead ->
            Cont realSealRead transport supportRead ->
              Cont supportRead nameRow replayRead ->
                Cont replayRead route compactRead ->
                  Cont compactRead mesh uniformRead ->
                    PkgSig bundle uniformRead pkg ->
                      UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                        UnaryHistory realSealRead ∧ UnaryHistory supportRead ∧
                          UnaryHistory replayRead ∧ UnaryHistory compactRead ∧
                            UnaryHistory uniformRead ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row dyadicRead ∨ hsame row streamRead ∨
                                    hsame row realSealRead ∨ hsame row replayRead ∨
                                      hsame row compactRead ∨ hsame row uniformRead)
                                (fun row : BHist =>
                                  hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier radiusMeshDyadic dyadicWindowStream streamRouteRealSeal
    realSealTransportSupport supportNameReplay replayRouteCompact compactMeshUniform
    uniformPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRealSeal
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed realSealUnary transportUnary realSealTransportSupport
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed supportUnary nameRowUnary supportNameReplay
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed replayUnary routeUnary replayRouteCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary meshUnary compactMeshUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row realSealRead ∨
            hsame row replayRead ∨ hsame row compactRead ∨ hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨dyadicUnary, streamUnary, realSealUnary, supportUnary, replayUnary, compactUnary,
      uniformUnary, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
