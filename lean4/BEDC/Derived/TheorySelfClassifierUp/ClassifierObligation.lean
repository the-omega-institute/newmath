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

theorem TheorySelfClassifier_classifier_obligation [AskSetup] [PackageSetup]
    {G E R P A L H C Q N classifierRead read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg ->
      Cont A L classifierRead ->
        Cont classifierRead N read ->
          PkgSig bundle read pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row read ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row G ∨ hsame row E ∨ hsame row R ∨ hsame row P ∨
                    hsame row A ∨ hsame row L ∨ hsame row classifierRead ∨
                      hsame row read)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont A L classifierRead ∧
                    Cont classifierRead N read ∧ PkgSig bundle read pkg)
                hsame ∧ UnaryHistory classifierRead ∧ UnaryHistory read := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier classifierRoute readRoute readPkg
  obtain ⟨_gUnary, _eUnary, _rUnary, _pUnary, aUnary, lUnary, _hUnary, _cUnary,
    _qUnary, nUnary, _generatorEqualityRoute, _recursorPurityRoute,
    _classifierCarrierRoute, _provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed aUnary lUnary classifierRoute
  have readUnary : UnaryHistory read :=
    unary_cont_closed classifierUnary nUnary readRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row E ∨ hsame row R ∨ hsame row P ∨
              hsame row A ∨ hsame row L ∨ hsame row classifierRead ∨ hsame row read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A L classifierRead ∧
              Cont classifierRead N read ∧ PkgSig bundle read pkg)
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, readRoute, readPkg⟩
  }
  exact ⟨cert, classifierUnary, readUnary⟩

end BEDC.Derived.TheorySelfClassifierUp
