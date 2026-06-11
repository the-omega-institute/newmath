import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionMetricCompletionRootRoute [AskSetup] [PackageSetup]
    {K E C R O L H T P N completionCover completionWitness completionOrder namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont K E completionCover →
        Cont completionCover R completionWitness →
          Cont completionWitness O completionOrder →
            Cont completionOrder N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                        hsame row O ∨ hsame row completionCover ∨
                          hsame row completionWitness ∨ hsame row completionOrder ∨
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K E completionCover ∧
                        Cont completionCover R completionWitness ∧
                          Cont completionWitness O completionOrder ∧
                            Cont completionOrder N namedRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory completionCover ∧ UnaryHistory completionWitness ∧
                    UnaryHistory completionOrder ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute witnessRoute orderRoute namedRoute namedPkg
  obtain ⟨KUnary, EUnary, _CUnary, RUnary, OUnary, _LUnary, _HUnary, _TUnary,
    _PUnary, NUnary, _KEC, _CRO, _OLT, _HTP, provenancePkg, _localNamePkg⟩ := carrier
  have completionCoverUnary : UnaryHistory completionCover :=
    unary_cont_closed KUnary EUnary coverRoute
  have completionWitnessUnary : UnaryHistory completionWitness :=
    unary_cont_closed completionCoverUnary RUnary witnessRoute
  have completionOrderUnary : UnaryHistory completionOrder :=
    unary_cont_closed completionWitnessUnary OUnary orderRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed completionOrderUnary NUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨
              hsame row completionCover ∨ hsame row completionWitness ∨
                hsame row completionOrder ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K E completionCover ∧
              Cont completionCover R completionWitness ∧
                Cont completionWitness O completionOrder ∧
                  Cont completionOrder N namedRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, witnessRoute, orderRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, completionCoverUnary, completionWitnessUnary, completionOrderUnary, namedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
