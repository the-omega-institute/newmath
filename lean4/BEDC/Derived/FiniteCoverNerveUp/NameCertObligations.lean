import BEDC.Derived.FiniteCoverNerveUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteCoverNerveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteCoverNerveCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K V O F R B U H C P Q : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory V ->
        UnaryHistory O ->
          UnaryHistory F ->
            UnaryHistory R ->
              UnaryHistory B ->
                UnaryHistory U ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      UnaryHistory P ->
                        UnaryHistory Q ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle Q pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row Q ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row K ∨ hsame row V ∨ hsame row O ∨
                                      hsame row F ∨ hsame row R ∨ hsame row B ∨
                                        hsame row U ∨ hsame row H ∨ hsame row C ∨
                                          hsame row P ∨ hsame row Q)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle Q pkg)
                                  hsame ∧ UnaryHistory K ∧ UnaryHistory V ∧
                                UnaryHistory O ∧ UnaryHistory F ∧ UnaryHistory R ∧
                                  UnaryHistory B ∧ UnaryHistory U := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro kUnary vUnary oUnary fUnary rUnary bUnary uUnary _hUnary _cUnary _pUnary qUnary
    provenancePkg localPkg
  have sourceLocal :
      (fun row : BHist => hsame row Q ∧ UnaryHistory row) Q := by
    exact ⟨hsame_refl Q, qUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row Q ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row V ∨ hsame row O ∨ hsame row F ∨ hsame row R ∨
              hsame row B ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row Q)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Q sourceLocal
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, localPkg⟩
  }
  exact ⟨cert, kUnary, vUnary, oUnary, fUnary, rUnary, bUnary, uUnary⟩

end BEDC.Derived.FiniteCoverNerveUp
