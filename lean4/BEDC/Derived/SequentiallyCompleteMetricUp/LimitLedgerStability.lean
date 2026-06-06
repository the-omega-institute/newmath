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

theorem SequentiallyCompleteMetricLimitLedgerStability [AskSetup] [PackageSetup]
    {X X' S S' M M' L L' D D' H H' C C' P P' N N' limitRead limitRead'
      distanceRead distanceRead' replayRead replayRead' namedRead namedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      sequentiallyCompleteMetricFields
          (SequentiallyCompleteMetricUp.mk X' S' M' L' D' H' C' P' N') =
        [X', S', M', L', D', H', C', P', N'] ->
      UnaryHistory L -> UnaryHistory D -> UnaryHistory C -> UnaryHistory N ->
      UnaryHistory L' -> UnaryHistory D' -> UnaryHistory C' -> UnaryHistory N' ->
      hsame L L' -> hsame D D' -> hsame C C' -> hsame N N' ->
      Cont L D distanceRead -> Cont distanceRead C replayRead ->
      Cont replayRead N namedRead -> Cont L' D' distanceRead' ->
      Cont distanceRead' C' replayRead' -> Cont replayRead' N' namedRead' ->
      PkgSig bundle P pkg -> PkgSig bundle P' pkg ->
      PkgSig bundle N pkg -> PkgSig bundle N' pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row D ∨ hsame row C ∨ hsame row N ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L D distanceRead ∧
              Cont distanceRead C replayRead ∧ Cont replayRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory namedRead ∧ UnaryHistory namedRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows fieldRows' lUnary dUnary cUnary nUnary lUnary' dUnary' cUnary'
    nUnary' _sameL _sameD _sameC _sameN distanceRoute replayRoute namedRoute
    distanceRoute' replayRoute' namedRoute' provenancePkg _provenancePkg' namePkg _namePkg'
  cases fieldRows
  cases fieldRows'
  have _displayedLimitReads : BHist × BHist := (limitRead, limitRead')
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed lUnary dUnary distanceRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary namedRoute
  have distanceUnary' : UnaryHistory distanceRead' :=
    unary_cont_closed lUnary' dUnary' distanceRoute'
  have replayUnary' : UnaryHistory replayRead' :=
    unary_cont_closed distanceUnary' cUnary' replayRoute'
  have namedUnary' : UnaryHistory namedRead' :=
    unary_cont_closed replayUnary' nUnary' namedRoute'
  constructor
  · exact {
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, distanceRoute, replayRoute, namedRoute, provenancePkg, namePkg⟩
    }
  · exact ⟨namedUnary, namedUnary'⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
