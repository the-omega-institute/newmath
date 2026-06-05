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

theorem SequentiallyCompleteMetricChoiceFreeUniquenessBoundary [AskSetup] [PackageSetup]
    {X S M L L' D D' H H' C C' P P' N N' limitRead limitRead'
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] →
      sequentiallyCompleteMetricFields
          (SequentiallyCompleteMetricUp.mk X S M L' D' H' C' P' N') =
        [X, S, M, L', D', H', C', P', N'] →
      UnaryHistory X →
      UnaryHistory S →
      UnaryHistory M →
      UnaryHistory L →
      UnaryHistory L' →
      UnaryHistory D →
      UnaryHistory D' →
      Cont S M limitRead →
      Cont S M limitRead' →
      Cont limitRead D comparisonRead →
      PkgSig bundle P pkg →
      PkgSig bundle P' pkg →
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row L' ∨
              hsame row D ∨ hsame row D' ∨ hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle P' pkg)
          hsame ∧
        UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows fieldRows' xUnary sUnary mUnary lUnary lUnary' dUnary dUnary'
    limitRoute limitRoute' comparisonRoute provenancePkg provenancePkg'
  cases fieldRows
  cases fieldRows'
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed sUnary mUnary limitRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed limitUnary dUnary comparisonRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro comparisonRead (And.intro (hsame_refl comparisonRead) comparisonUnary)
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, provenancePkg'⟩
    }
  · exact comparisonUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
