import BEDC.Derived.NonAxiomAdmissionUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NonAxiomAdmissionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NonAxiomAdmissionWitnessRoute_nonescape [AskSetup] [PackageSetup]
    {admission : NonAxiomAdmissionUp} {X F W H C P N consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    admission = NonAxiomAdmissionUp.mk X F W H C P N →
      UnaryHistory W →
        UnaryHistory H →
          UnaryHistory P →
            Cont W H C →
              Cont C P consumerRead →
                PkgSig bundle consumerRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row W ∨ hsame row C ∨ hsame row consumerRead ∨
                            hsame row N) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row H ∨
                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W H C ∧ Cont C P consumerRead ∧
                          PkgSig bundle consumerRead pkg)
                      hsame ∧
                    UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _admissionEq unaryW unaryH unaryP contWHC contCPConsumer consumerPkg
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryW unaryH contWHC
  have unaryConsumer : UnaryHistory consumerRead :=
    unary_cont_closed unaryC unaryP contCPConsumer
  have sourceAtConsumer :
      (hsame consumerRead W ∨ hsame consumerRead C ∨ hsame consumerRead consumerRead ∨
            hsame consumerRead N) ∧
        UnaryHistory consumerRead :=
    ⟨Or.inr (Or.inr (Or.inl (hsame_refl consumerRead))), unaryConsumer⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row W ∨ hsame row C ∨ hsame row consumerRead ∨ hsame row N) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row W ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W H C ∧ Cont C P consumerRead ∧
              PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
        cases source with
        | intro displayed rowUnary =>
            have otherUnary : UnaryHistory _other :=
              unary_transport rowUnary sameRows
            have otherDisplayed :
                hsame _other W ∨ hsame _other C ∨ hsame _other consumerRead ∨
                  hsame _other N := by
              cases displayed with
              | inl sameW =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameW)
              | inr rest =>
                  cases rest with
                  | inl sameC =>
                      exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameC))
                  | inr rest2 =>
                      cases rest2 with
                      | inl sameConsumer =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameConsumer)))
                      | inr sameN =>
                          exact
                            Or.inr
                              (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameN)))
            exact ⟨otherDisplayed, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameW =>
          exact Or.inr (Or.inr (Or.inl sameW))
      | inr rest =>
          cases rest with
          | inl sameC =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameC))))
          | inr rest2 =>
              cases rest2 with
              | inl sameConsumer =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr sameConsumer))))))
              | inr sameN =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inl sameN))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, contWHC, contCPConsumer, consumerPkg⟩
  }
  exact ⟨cert, unaryConsumer⟩

end BEDC.Derived.NonAxiomAdmissionUp
