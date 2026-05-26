import BEDC.Derived.CauchyConvergenceCriterionUp.TasteGate

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_specker_boundary [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      speckerRead locatedRequest : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg →
      Cont sealRow route speckerRead →
        Cont speckerRead localCert locatedRequest →
          PkgSig bundle locatedRequest pkg →
            SemanticNameCert
                (fun row : BHist => hsame row locatedRequest ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row schedule ∨ hsame row dyadic ∨ hsame row handoff ∨
                    hsame row sealRow ∨ hsame row speckerRead ∨
                      hsame row locatedRequest)
                (fun row : BHist => hsame row locatedRequest ∧
                  PkgSig bundle locatedRequest pkg)
                hsame ∧
              UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory speckerRead ∧
                  UnaryHistory locatedRequest ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier sealSpecker speckerLocated locatedPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, provenanceUnary, localCertUnary, _scheduleModulusDyadic,
    _dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have speckerUnary : UnaryHistory speckerRead :=
    unary_cont_closed sealUnary routeUnary sealSpecker
  have locatedUnary : UnaryHistory locatedRequest :=
    unary_cont_closed speckerUnary localCertUnary speckerLocated
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRequest ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row dyadic ∨ hsame row handoff ∨
              hsame row sealRow ∨ hsame row speckerRead ∨ hsame row locatedRequest)
          (fun row : BHist => hsame row locatedRequest ∧ PkgSig bundle locatedRequest pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro locatedRequest
          (And.intro (hsame_refl locatedRequest) locatedUnary)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left locatedPkg
  }
  exact
    ⟨cert, scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary, speckerUnary,
      locatedUnary, provenancePkg⟩

theorem CauchyConvergenceCriterionCarrier_located_modulus_frontier [AskSetup]
    [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert locatedRead
      speckerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg →
      Cont schedule modulus locatedRead →
        Cont handoff route speckerRead →
          PkgSig bundle locatedRead pkg →
            hsame locatedRead dyadic ∧ UnaryHistory locatedRead ∧
              UnaryHistory speckerRead ∧ Cont schedule modulus locatedRead ∧
                Cont handoff route speckerRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle locatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro carrier locatedRoute speckerRoute locatedPkg
  obtain ⟨scheduleUnary, modulusUnary, _dyadicUnary, handoffUnary, _sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    _dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have sameLocatedDyadic : hsame locatedRead dyadic :=
    cont_deterministic locatedRoute scheduleModulusDyadic
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed scheduleUnary modulusUnary locatedRoute
  have speckerUnary : UnaryHistory speckerRead :=
    unary_cont_closed handoffUnary routeUnary speckerRoute
  exact
    ⟨sameLocatedDyadic, locatedUnary, speckerUnary, locatedRoute, speckerRoute,
      provenancePkg, locatedPkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
