import BEDC.Derived.CauchyConvergenceCriterionUp.ScopedReadbackStrengthening

namespace BEDC.Derived.CauchyConvergenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyConvergenceCriterionCarrier_scoped_closure [AskSetup] [PackageSetup]
    {schedule modulus dyadic handoff sealRow transportRow route provenance localCert
      regularRead completionRead nullRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvergenceCriterionCarrier schedule modulus dyadic handoff sealRow transportRow
        route provenance localCert bundle pkg ->
      Cont handoff route regularRead ->
        Cont sealRow route completionRead ->
          Cont schedule modulus nullRead ->
            PkgSig bundle regularRead pkg ->
              PkgSig bundle completionRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row schedule ∨ hsame row modulus ∨ hsame row dyadic ∨
                        hsame row handoff ∨ hsame row sealRow ∨
                          Cont sealRow route completionRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                        hsame row completionRead)
                    hsame ∧
                  UnaryHistory schedule ∧ UnaryHistory modulus ∧ UnaryHistory dyadic ∧
                    UnaryHistory handoff ∧ UnaryHistory sealRow ∧ UnaryHistory regularRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory nullRead ∧
                        hsame nullRead dyadic ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier handoffRouteRegular sealRouteCompletion scheduleModulusNull _regularPkg
    completionPkg
  obtain ⟨scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _localCertUnary, scheduleModulusDyadic,
    _dyadicHandoffSeal, _sealTransportRoute, _routeProvenanceLocal, _sameSealHandoff,
    _sameSealProvenance, provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed handoffUnary routeUnary handoffRouteRegular
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary routeUnary sealRouteCompletion
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed scheduleUnary modulusUnary scheduleModulusNull
  have sameNullDyadic : hsame nullRead dyadic :=
    cont_deterministic scheduleModulusNull scheduleModulusDyadic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row schedule ∨ hsame row modulus ∨ hsame row dyadic ∨
              hsame row handoff ∨ hsame row sealRow ∨
                Cont sealRow route completionRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
              hsame row completionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRouteCompletion))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, completionPkg, source.left⟩
  }
  exact
    ⟨cert, scheduleUnary, modulusUnary, dyadicUnary, handoffUnary, sealUnary,
      regularUnary, completionUnary, nullUnary, sameNullDyadic, provenancePkg⟩

end BEDC.Derived.CauchyConvergenceCriterionUp
