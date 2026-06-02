import BEDC.Derived.RegularCauchyInterleavingUp

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterleavingPacket_completion_selector_nonescape [AskSetup]
    [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint selectorRead mergedWindow
      tailBudget completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg →
      Cont selector modulus selectorRead →
        Cont selectorRead endpoint mergedWindow →
          Cont mergedWindow nameCert tailBudget →
            Cont tailBudget provenance completionRead →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row selector ∨ hsame row modulus ∨ hsame row endpoint ∨
                        hsame row selectorRead ∨ hsame row mergedWindow ∨
                          hsame row tailBudget ∨ hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont selector modulus selectorRead ∧
                        Cont selectorRead endpoint mergedWindow ∧
                          Cont mergedWindow nameCert tailBudget ∧
                            Cont tailBudget provenance completionRead ∧
                              PkgSig bundle completionRead pkg)
                    hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory mergedWindow ∧
                      UnaryHistory tailBudget ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: RegularCauchyInterleavingPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet selectorRoute mergedRoute tailRoute completionRoute completionPkg
  obtain ⟨_leftNameUnary, _rightNameUnary, leftScheduleUnary, rightScheduleUnary,
    selectorUnary, modulusUnary, _transportUnary, _routesUnary, provenanceUnary,
    nameCertUnary, leftSealRoute, rightSealRoute, interleavedRoute, endpointRoute,
    _endpointPkg⟩ := packet
  have leftSealUnary : UnaryHistory leftSeal :=
    unary_cont_closed selectorUnary leftScheduleUnary leftSealRoute
  have rightSealUnary : UnaryHistory rightSeal :=
    unary_cont_closed selectorUnary rightScheduleUnary rightSealRoute
  have interleavedUnary : UnaryHistory interleavedSeal :=
    unary_cont_closed leftSealUnary rightSealUnary interleavedRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed interleavedUnary modulusUnary endpointRoute
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed selectorUnary modulusUnary selectorRoute
  have mergedWindowUnary : UnaryHistory mergedWindow :=
    unary_cont_closed selectorReadUnary endpointUnary mergedRoute
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed mergedWindowUnary nameCertUnary tailRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed tailBudgetUnary provenanceUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row selector ∨ hsame row modulus ∨ hsame row endpoint ∨
              hsame row selectorRead ∨ hsame row mergedWindow ∨ hsame row tailBudget ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont selector modulus selectorRead ∧
              Cont selectorRead endpoint mergedWindow ∧ Cont mergedWindow nameCert tailBudget ∧
                Cont tailBudget provenance completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectorRoute, mergedRoute, tailRoute, completionRoute,
          completionPkg⟩
  }
  exact ⟨cert, selectorReadUnary, mergedWindowUnary, tailBudgetUnary, completionReadUnary⟩

end BEDC.Derived.RegularCauchyInterleavingUp
