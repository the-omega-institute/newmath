import BEDC.Derived.SequentiallyCompleteMetricUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricRegSeqRatHandoff [AskSetup] [PackageSetup]
    {X S M L D H C P N sequenceRead regseqRead limitRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory N ->
                Cont X S sequenceRead ->
                  Cont sequenceRead M regseqRead ->
                    Cont regseqRead L limitRead ->
                      Cont limitRead N namedRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row S ∨ hsame row M ∨
                                    hsame row L ∨ hsame row N ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont X S sequenceRead ∧
                                    Cont sequenceRead M regseqRead ∧
                                      Cont regseqRead L limitRead ∧
                                        Cont limitRead N namedRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory regseqRead ∧ UnaryHistory limitRead ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro fields xUnary sUnary mUnary lUnary nUnary sequenceRoute regseqRoute limitRoute
    namedRoute provenancePkg namePkg
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed xUnary sUnary sequenceRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed sequenceUnary mUnary regseqRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed regseqUnary lUnary limitRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed limitUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row N ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S sequenceRead ∧ Cont sequenceRead M regseqRead ∧
              Cont regseqRead L limitRead ∧ Cont limitRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sequenceRoute, regseqRoute, limitRoute, namedRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, regseqUnary, limitUnary, namedUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
