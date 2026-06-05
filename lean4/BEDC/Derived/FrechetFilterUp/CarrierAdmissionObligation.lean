import BEDC.Derived.FrechetFilterUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterCarrierAdmissionObligation [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N admissionRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    frechetFilterFields (FrechetFilterUp.mk U T S M B Q R A H C P N) =
        [U, T, S, M, B, Q, R, A, H, C, P, N] ->
      UnaryHistory U ->
        UnaryHistory T ->
          UnaryHistory S ->
            Cont U T admissionRead ->
              Cont admissionRead S handoffRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle N pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
                            hsame row B ∨ hsame row Q ∨ hsame row R ∨ hsame row A ∨
                              hsame row handoffRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont U T admissionRead ∧
                            Cont admissionRead S handoffRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows uUnary tUnary sUnary admissionRoute handoffRoute provenancePkg namePkg
  cases fieldRows
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed uUnary tUnary admissionRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed admissionUnary sUnary handoffRoute
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, admissionRoute, handoffRoute, provenancePkg, namePkg⟩
    }
  · exact handoffUnary

end BEDC.Derived.FrechetFilterUp
