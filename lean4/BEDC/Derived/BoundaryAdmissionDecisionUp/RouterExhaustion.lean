import BEDC.Derived.BoundaryAdmissionDecisionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BoundaryAdmissionDecisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BoundaryAdmissionDecision_router_exhaustion [AskSetup] [PackageSetup]
    {X F R A H C P N chosenRead requestedRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X F chosenRead →
      Cont chosenRead R requestedRead →
        Cont requestedRead A auditRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row auditRead ∧ Cont X F chosenRead ∧
                      Cont chosenRead R requestedRead ∧
                        Cont requestedRead A auditRead)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row R ∨ hsame row A ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row auditRead)
                  (fun row : BHist =>
                    hsame row auditRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
                  hsame ∧
                Cont X F chosenRead ∧ Cont chosenRead R requestedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro chosenRoute requestedRoute auditRoute provenancePkg namePkg
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row auditRead ∧ Cont X F chosenRead ∧
              Cont chosenRead R requestedRead ∧ Cont requestedRead A auditRead)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row R ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row auditRead)
          (fun row : BHist =>
            hsame row auditRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro auditRead
          ⟨hsame_refl auditRead, chosenRoute, requestedRoute, auditRoute⟩
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
            source.right.left,
            source.right.right.left,
            source.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }
  exact ⟨cert, chosenRoute, requestedRoute⟩

theorem BoundaryAdmissionDecision_obligation_axis_sync [AskSetup] [PackageSetup]
    {X F R A H C P N chosenRead requestedRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X F chosenRead →
      Cont chosenRead R requestedRead →
        Cont requestedRead A auditRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row auditRead ∧ Cont X F chosenRead ∧
                      Cont chosenRead R requestedRead ∧
                        Cont requestedRead A auditRead)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row R ∨ hsame row A ∨
                      hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                        hsame row auditRead)
                  (fun row : BHist =>
                    hsame row auditRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
                  hsame ∧
                Cont X F chosenRead ∧ Cont chosenRead R requestedRead ∧
                  Cont requestedRead A auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro chosenRoute requestedRoute auditRoute provenancePkg namePkg
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row auditRead ∧ Cont X F chosenRead ∧
              Cont chosenRead R requestedRead ∧ Cont requestedRead A auditRead)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row R ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row auditRead)
          (fun row : BHist =>
            hsame row auditRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro auditRead
          ⟨hsame_refl auditRead, chosenRoute, requestedRoute, auditRoute⟩
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
            source.right.left,
            source.right.right.left,
            source.right.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }
  exact ⟨cert, chosenRoute, requestedRoute, auditRoute⟩

end BEDC.Derived.BoundaryAdmissionDecisionUp
