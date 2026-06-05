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

theorem SequentiallyCompleteMetricTailFusion [AskSetup] [PackageSetup]
    {X S M M' L L' D D' H H' C C' P P' N N' tailRead modulusRead modulusRead'
      distanceRead distanceRead' replayRead replayRead' handoffRead handoffRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory S -> UnaryHistory M -> UnaryHistory M' ->
      UnaryHistory D -> UnaryHistory D' -> UnaryHistory C -> UnaryHistory C' ->
      UnaryHistory N -> UnaryHistory N' -> Cont X S tailRead ->
      Cont tailRead M modulusRead -> Cont tailRead M' modulusRead' ->
      Cont modulusRead D distanceRead -> Cont modulusRead' D' distanceRead' ->
      Cont distanceRead C replayRead -> Cont distanceRead' C' replayRead' ->
      Cont replayRead N handoffRead -> Cont replayRead' N' handoffRead' ->
      PkgSig bundle P pkg -> PkgSig bundle P' pkg ->
      PkgSig bundle N pkg -> PkgSig bundle N' pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row M' ∨
              hsame row D ∨ hsame row D' ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X S tailRead ∧
              Cont tailRead M modulusRead ∧ Cont tailRead M' modulusRead' ∧
                Cont modulusRead D distanceRead ∧ Cont modulusRead' D' distanceRead' ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory handoffRead ∧ UnaryHistory handoffRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro xUnary sUnary mUnary mUnary' dUnary dUnary' cUnary cUnary' nUnary nUnary'
    tailRoute modulusRoute modulusRoute' distanceRoute distanceRoute' replayRoute replayRoute'
    handoffRoute handoffRoute' provenancePkg _provenancePkg' namePkg _namePkg'
  have _carrierRows : List BHist := [L, L', H, H']
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed xUnary sUnary tailRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed tailUnary mUnary modulusRoute
  have modulusUnary' : UnaryHistory modulusRead' :=
    unary_cont_closed tailUnary mUnary' modulusRoute'
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed modulusUnary dUnary distanceRoute
  have distanceUnary' : UnaryHistory distanceRead' :=
    unary_cont_closed modulusUnary' dUnary' distanceRoute'
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed distanceUnary cUnary replayRoute
  have replayUnary' : UnaryHistory replayRead' :=
    unary_cont_closed distanceUnary' cUnary' replayRoute'
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed replayUnary nUnary handoffRoute
  have handoffUnary' : UnaryHistory handoffRead' :=
    unary_cont_closed replayUnary' nUnary' handoffRoute'
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
          ⟨source.right, tailRoute, modulusRoute, modulusRoute', distanceRoute,
            distanceRoute', provenancePkg, namePkg⟩
    }
  · exact ⟨handoffUnary, handoffUnary'⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
