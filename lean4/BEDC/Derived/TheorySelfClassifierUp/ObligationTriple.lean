import BEDC.Derived.TheorySelfClassifierUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_obligation_triple [AskSetup] [PackageSetup]
    {G E R P A L H C Q N read : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg ->
      Cont L N read ->
        PkgSig bundle read pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row read ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row G ∨ hsame row E ∨ hsame row R ∨ hsame row P ∨
                  hsame row A ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                    hsame row Q ∨ hsame row N ∨ hsame row read)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont G E R ∧ Cont R P A ∧ Cont A L C ∧
                  Cont L N read ∧ PkgSig bundle Q pkg ∧ PkgSig bundle read pkg)
              hsame ∧
            UnaryHistory G ∧ UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory P ∧
              UnaryHistory A ∧ UnaryHistory L ∧ UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier ledgerRoute readPkg
  obtain ⟨gUnary, eUnary, rUnary, pUnary, aUnary, lUnary, _hUnary, _cUnary,
    _qUnary, nUnary, generatorEqualityRoute, recursorPurityRoute, classifierRoute,
    provenancePkg⟩ := carrier
  have readUnary : UnaryHistory read :=
    unary_cont_closed lUnary nUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row E ∨ hsame row R ∨ hsame row P ∨ hsame row A ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N ∨
                hsame row read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G E R ∧ Cont R P A ∧ Cont A L C ∧
              Cont L N read ∧ PkgSig bundle Q pkg ∧ PkgSig bundle read pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro read ⟨hsame_refl read, readUnary⟩
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
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, generatorEqualityRoute, recursorPurityRoute, classifierRoute,
          ledgerRoute, provenancePkg, readPkg⟩
  }
  exact ⟨cert, gUnary, eUnary, rUnary, pUnary, aUnary, lUnary, readUnary⟩

end BEDC.Derived.TheorySelfClassifierUp
