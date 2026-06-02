import BEDC.Derived.HausdorffCompletionEnvelopeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffCompletionEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffCompletionEnvelopeNameCertObligations [AskSetup] [PackageSetup]
    {hausdorff separated metric stream dyadic regseq realSeal transport replay provenance
      localName separatedRead completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont hausdorff separated separatedRead →
      Cont separatedRead metric completionRead →
        Cont regseq realSeal realRead →
          UnaryHistory hausdorff →
            UnaryHistory separated →
              UnaryHistory metric →
                UnaryHistory regseq →
                  UnaryHistory realSeal →
                    PkgSig bundle realRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row hausdorff ∨ hsame row separated ∨
                              hsame row metric ∨ hsame row stream ∨ hsame row dyadic ∨
                                hsame row regseq ∨ hsame row realSeal ∨
                                  hsame row separatedRead ∨ hsame row completionRead ∨
                                    hsame row realRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont hausdorff separated separatedRead ∧
                              Cont separatedRead metric completionRead ∧
                                Cont regseq realSeal realRead ∧
                                  PkgSig bundle realRead pkg)
                          hsame ∧
                        UnaryHistory separatedRead ∧ UnaryHistory completionRead ∧
                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro separatedRoute completionRoute realRoute hausdorffUnary separatedUnary metricUnary
    regseqUnary realSealUnary realPkg
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed hausdorffUnary separatedUnary separatedRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedReadUnary metricUnary completionRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary realSealUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row hausdorff ∨ hsame row separated ∨ hsame row metric ∨
              hsame row stream ∨ hsame row dyadic ∨ hsame row regseq ∨
                hsame row realSeal ∨ hsame row separatedRead ∨
                  hsame row completionRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont hausdorff separated separatedRead ∧
              Cont separatedRead metric completionRead ∧ Cont regseq realSeal realRead ∧
                PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, separatedRoute, completionRoute, realRoute, realPkg⟩
  }
  exact ⟨cert, separatedReadUnary, completionReadUnary, realReadUnary⟩

end BEDC.Derived.HausdorffCompletionEnvelopeUp
