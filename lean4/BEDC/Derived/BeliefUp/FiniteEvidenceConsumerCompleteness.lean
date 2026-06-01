import BEDC.Derived.BeliefUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.BeliefUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem BeliefFiniteEvidenceConsumerCompleteness [AskSetup] [PackageSetup]
    {prior observation update probability posterior evidence ledger namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory prior ->
      UnaryHistory observation ->
        UnaryHistory probability ->
          UnaryHistory evidence ->
            Cont prior observation update ->
              Cont update probability posterior ->
                Cont posterior evidence ledger ->
                  Cont ledger evidence namedRead ->
                    SigRel bundle ledger posterior ->
                      PkgSig bundle posterior pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row posterior ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row prior ∨ hsame row observation ∨ hsame row update ∨
                                hsame row probability ∨ hsame row posterior ∨
                                  hsame row evidence ∨ hsame row ledger ∨ hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont prior observation update ∧
                                Cont update probability posterior ∧
                                  Cont posterior evidence ledger ∧
                                    Cont ledger evidence namedRead ∧
                                      SigRel bundle ledger posterior ∧
                                        PkgSig bundle posterior pkg)
                            hsame ∧
                          UnaryHistory update ∧ UnaryHistory posterior ∧ UnaryHistory ledger ∧
                            UnaryHistory namedRead ∧ SigRel bundle ledger posterior ∧
                              PkgSig bundle posterior pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SigRel PkgSig SemanticNameCert hsame UnaryHistory
  intro priorUnary observationUnary probabilityUnary evidenceUnary updateRoute posteriorRoute
  intro ledgerRoute namedRoute ledgerSig posteriorPkg
  have updateUnary : UnaryHistory update :=
    unary_cont_closed priorUnary observationUnary updateRoute
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed updateUnary probabilityUnary posteriorRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed posteriorUnary evidenceUnary ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary evidenceUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row posterior ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row prior ∨ hsame row observation ∨ hsame row update ∨
              hsame row probability ∨ hsame row posterior ∨ hsame row evidence ∨
                hsame row ledger ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont prior observation update ∧
              Cont update probability posterior ∧ Cont posterior evidence ledger ∧
                Cont ledger evidence namedRead ∧ SigRel bundle ledger posterior ∧
                  PkgSig bundle posterior pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro posterior
        ⟨hsame_refl posterior, posteriorUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, updateRoute, posteriorRoute, ledgerRoute, namedRoute, ledgerSig,
          posteriorPkg⟩
  }
  exact
    ⟨cert, updateUnary, posteriorUnary, ledgerUnary, namedUnary, ledgerSig, posteriorPkg⟩

end BEDC.Derived.BeliefUp
