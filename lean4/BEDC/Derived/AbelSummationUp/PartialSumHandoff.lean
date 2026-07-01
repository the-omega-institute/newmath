import BEDC.Derived.AbelSummationUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelSummationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AbelSummationPartialSumHandoff [AskSetup] [PackageSetup]
    {S A D B T R E H C P N handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory A ->
        UnaryHistory D ->
          UnaryHistory B ->
            UnaryHistory T ->
              UnaryHistory R ->
                UnaryHistory E ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      UnaryHistory P ->
                        UnaryHistory N ->
                          Cont S A D ->
                            Cont D B T ->
                              Cont T R E ->
                                Cont T R handoffRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle N pkg ->
                                      PkgSig bundle handoffRead pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row handoffRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row S ∨ hsame row A ∨
                                                hsame row D ∨ hsame row B ∨
                                                  hsame row T ∨ hsame row R ∨
                                                    hsame row E ∨ hsame row H ∨
                                                      hsame row C ∨ hsame row P ∨
                                                        hsame row N ∨
                                                          hsame row handoffRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont S A D ∧
                                                Cont D B T ∧ Cont T R handoffRead ∧
                                                  PkgSig bundle handoffRead pkg)
                                            hsame ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro sUnary _aUnary dUnary bUnary tUnary rUnary _eUnary _hUnary _cUnary
    _pUnary _nUnary sourceRoute boundaryRoute _sealRoute handoffRoute _pPkg _nPkg
    handoffPkg
  have boundaryUnary : UnaryHistory T :=
    unary_cont_closed dUnary bUnary boundaryRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed boundaryUnary rUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row D ∨ hsame row B ∨
              hsame row T ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S A D ∧ Cont D B T ∧ Cont T R handoffRead ∧
              PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, boundaryRoute, handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.AbelSummationUp
