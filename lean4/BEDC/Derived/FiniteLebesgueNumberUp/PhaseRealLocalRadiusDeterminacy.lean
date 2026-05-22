import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealLocalRadiusDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead
      realSealRead supportRead replayRead localNameRead otherReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh dyadicRead →
        Cont dyadicRead window streamRead →
          Cont streamRead route realSealRead →
            Cont realSealRead transport supportRead →
              Cont supportRead nameRow replayRead →
                hsame otherReplay replayRead →
                  PkgSig bundle localNameRead pkg →
                    PkgSig bundle replayRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row otherReplay ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row dyadicRead ∨ hsame row streamRead ∨
                              hsame row realSealRead ∨ hsame row replayRead ∨
                                hsame row otherReplay)
                          (fun row : BHist =>
                            PkgSig bundle replayRead pkg ∧ hsame row otherReplay)
                          hsame ∧
                        UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                          UnaryHistory realSealRead ∧ UnaryHistory supportRead ∧
                            UnaryHistory replayRead ∧ UnaryHistory otherReplay ∧
                              hsame replayRead otherReplay ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localNameRead pkg ∧
                                    PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshDyadic dyadicWindowStream streamRouteSeal sealTransportSupport
    supportNameReplay sameOtherReplay localNamePkg replayPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed streamUnary routeUnary streamRouteSeal
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed realSealUnary transportUnary sealTransportSupport
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed supportUnary nameRowUnary supportNameReplay
  have otherReplayUnary : UnaryHistory otherReplay :=
    unary_transport_symm replayUnary sameOtherReplay
  have sameReplayOther : hsame replayRead otherReplay :=
    hsame_symm sameOtherReplay
  have otherReplayCarrier :
      (fun row : BHist => hsame row otherReplay ∧ UnaryHistory row) otherReplay := by
    exact ⟨hsame_refl otherReplay, otherReplayUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row otherReplay ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row realSealRead ∨
            hsame row replayRead ∨ hsame row otherReplay)
        (fun row : BHist => PkgSig bundle replayRead pkg ∧ hsame row otherReplay)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro otherReplay otherReplayCarrier
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨replayPkg, source.left⟩
    }
  exact
    ⟨cert, dyadicUnary, streamUnary, realSealUnary, supportUnary, replayUnary,
      otherReplayUnary, sameReplayOther, provenancePkg, localNamePkg, replayPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
