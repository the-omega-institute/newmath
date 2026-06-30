import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      PkgSig bundle N pkg →
        SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier namePkg
  obtain ⟨_epsilonUnary, _wUnary, _rUnary, _dUnary, _aUnary, _sigmaUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _carrierPkg⟩ := carrier
  refine
    { core :=
        { carrier_inhabited := ⟨N, hsame_refl N, nUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left))))))))
  · intro _row sourceRow
    exact ⟨sourceRow.right, namePkg⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
