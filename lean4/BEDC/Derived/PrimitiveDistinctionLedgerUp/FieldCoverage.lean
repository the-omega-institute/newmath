import BEDC.Derived.PrimitiveDistinctionLedgerUp.NoBooleanCollapse

namespace BEDC.Derived.PrimitiveDistinctionLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PrimitiveDistinctionLedger_field_coverage [AskSetup] [PackageSetup]
    {zero one distinction trace refusal replay localName markRead traceRead namedRead fieldRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory zero →
      UnaryHistory one →
        UnaryHistory distinction →
          UnaryHistory trace →
            UnaryHistory refusal →
              UnaryHistory replay →
                UnaryHistory localName →
                  Cont zero one markRead →
                    Cont trace refusal traceRead →
                      Cont replay localName namedRead →
                        Cont markRead traceRead fieldRead →
                          PkgSig bundle namedRead pkg →
                            PkgSig bundle fieldRead pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row fieldRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row markRead ∨ hsame row traceRead ∨
                                      hsame row namedRead ∨ hsame row fieldRead)
                                  (fun row : BHist =>
                                    Cont zero one markRead ∧ Cont trace refusal traceRead ∧
                                      Cont replay localName namedRead ∧
                                        Cont markRead traceRead fieldRead ∧
                                          PkgSig bundle fieldRead pkg ∧ hsame row fieldRead)
                                  hsame ∧
                                UnaryHistory markRead ∧ UnaryHistory traceRead ∧
                                  UnaryHistory namedRead ∧ UnaryHistory fieldRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro zeroUnary oneUnary _distinctionUnary traceUnary refusalUnary replayUnary
    localNameUnary markReadCont traceReadCont namedReadCont fieldReadCont _namedReadPkg
    fieldReadPkg
  have markReadUnary : UnaryHistory markRead :=
    unary_cont_closed zeroUnary oneUnary markReadCont
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary refusalUnary traceReadCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary localNameUnary namedReadCont
  have fieldReadUnary : UnaryHistory fieldRead :=
    unary_cont_closed markReadUnary traceReadUnary fieldReadCont
  have sourceAtField : hsame fieldRead fieldRead ∧ UnaryHistory fieldRead :=
    ⟨hsame_refl fieldRead, fieldReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fieldRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row markRead ∨ hsame row traceRead ∨ hsame row namedRead ∨
              hsame row fieldRead)
          (fun row : BHist =>
            Cont zero one markRead ∧ Cont trace refusal traceRead ∧
              Cont replay localName namedRead ∧ Cont markRead traceRead fieldRead ∧
                PkgSig bundle fieldRead pkg ∧ hsame row fieldRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fieldRead sourceAtField
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨markReadCont, traceReadCont, namedReadCont, fieldReadCont, fieldReadPkg,
          source.left⟩
  }
  exact ⟨cert, markReadUnary, traceReadUnary, namedReadUnary, fieldReadUnary⟩

end BEDC.Derived.PrimitiveDistinctionLedgerUp
