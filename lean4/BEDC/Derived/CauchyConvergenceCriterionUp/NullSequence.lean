import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_nullsequence_factorization [AskSetup]
    [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      nullRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg →
      hsame handoff BHist.Empty →
        Cont BHist.Empty dyadic handoff →
          Cont handoff route nullRead →
            PkgSig bundle nullRead pkg →
              SemanticNameCert
                  (fun row : BHist => UnaryHistory handoff ∧ hsame row handoff)
                  (fun row : BHist => UnaryHistory handoff ∧ hsame row handoff)
                  (fun row : BHist => UnaryHistory handoff ∧ hsame row handoff)
                  hsame ∧
                UnaryHistory nullRead ∧ hsame handoff BHist.Empty ∧
                  Cont BHist.Empty dyadic handoff ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle nullRead pkg := by
  -- BEDC touchpoint anchor: BHist.Empty Cont UnaryHistory ProbeBundle Pkg SemanticNameCert hsame
  intro carrier sameHandoffEmpty emptyDyadicHandoff handoffRoute nullPkg
  obtain ⟨_scheduleUnary, _modulusUnary, _dyadicUnary, handoffUnary, _sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, _scheduleModulusDyadic,
    _dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed handoffUnary routeUnary handoffRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => UnaryHistory handoff ∧ hsame row handoff)
        (fun row : BHist => UnaryHistory handoff ∧ hsame row handoff)
        (fun row : BHist => UnaryHistory handoff ∧ hsame row handoff)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoff (And.intro handoffUnary (hsame_refl handoff))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, nullUnary, sameHandoffEmpty, emptyDyadicHandoff, provenancePkg, nullPkg⟩

theorem CauchyConvergenceCriterionCarrier_null_sequence_scope [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      zeroDiff nullPacket : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg →
      Cont handoff dyadic zeroDiff →
        Cont zeroDiff schedule nullPacket →
          PkgSig bundle nullPacket pkg →
            UnaryHistory zeroDiff ∧ UnaryHistory nullPacket ∧
              Cont handoff dyadic zeroDiff ∧ Cont zeroDiff schedule nullPacket ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nullPacket pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier handoffDyadicZero zeroScheduleNull nullPkg
  obtain ⟨scheduleUnary, _modulusUnary, dyadicUnary, handoffUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _scheduleModulusDyadic,
    _dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroDiff :=
    unary_cont_closed handoffUnary dyadicUnary handoffDyadicZero
  have nullUnary : UnaryHistory nullPacket :=
    unary_cont_closed zeroUnary scheduleUnary zeroScheduleNull
  exact
    ⟨zeroUnary, nullUnary, handoffDyadicZero, zeroScheduleNull, provenancePkg, nullPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
