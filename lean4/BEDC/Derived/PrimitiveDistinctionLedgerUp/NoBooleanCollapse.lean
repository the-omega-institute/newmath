import BEDC.Derived.PrimitiveDistinctionLedgerUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PrimitiveDistinctionLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PrimitiveDistinctionLedger_no_boolean_collapse [AskSetup] [PackageSetup]
    {zero one distinction trace refusal replay localName markRead traceRead namedRead : BHist}
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
                        PkgSig bundle namedRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row markRead ∨ hsame row traceRead ∨
                                  hsame row namedRead ∨ hsame row refusal)
                              (fun row : BHist =>
                                Cont trace refusal traceRead ∧ PkgSig bundle namedRead pkg ∧
                                  hsame row refusal)
                              hsame ∧
                            UnaryHistory markRead ∧ UnaryHistory traceRead ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg
  intro zeroUnary oneUnary _distinctionUnary traceUnary refusalUnary replayUnary
    localNameUnary markReadCont traceReadCont namedReadCont namedReadPkg
  have markReadUnary : UnaryHistory markRead :=
    unary_cont_closed zeroUnary oneUnary markReadCont
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary refusalUnary traceReadCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary localNameUnary namedReadCont
  have sourceAtRefusal : hsame refusal refusal ∧ UnaryHistory refusal :=
    ⟨hsame_refl refusal, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row markRead ∨ hsame row traceRead ∨ hsame row namedRead ∨
              hsame row refusal)
          (fun row : BHist =>
            Cont trace refusal traceRead ∧ PkgSig bundle namedRead pkg ∧
              hsame row refusal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusal sourceAtRefusal
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
      exact ⟨traceReadCont, namedReadPkg, source.left⟩
  }
  exact ⟨cert, markReadUnary, traceReadUnary, namedReadUnary⟩

end BEDC.Derived.PrimitiveDistinctionLedgerUp
