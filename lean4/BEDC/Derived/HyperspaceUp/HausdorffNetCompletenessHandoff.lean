import BEDC.Derived.HyperspaceUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceHausdorffNetCompletenessHandoff [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M leftNet rightNet completeRead
      hausdorffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 N0 leftNet →
        Cont K1 N1 rightNet →
          Cont X R completeRead →
            Cont leftNet rightNet hausdorffRead →
              PkgSig bundle hausdorffRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row hausdorffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                        hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                          hsame row completeRead ∨ hsame row hausdorffRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle hausdorffRead pkg)
                    hsame ∧
                  UnaryHistory completeRead ∧ UnaryHistory hausdorffRead := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle Pkg SemanticNameCert
  intro carrier leftRoute rightRoute completeRoute hausdorffRoute hausdorffPkg
  obtain ⟨xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, _provenancePkg⟩ := carrier
  have leftUnary : UnaryHistory leftNet :=
    unary_cont_closed k0Unary n0Unary leftRoute
  have rightUnary : UnaryHistory rightNet :=
    unary_cont_closed k1Unary n1Unary rightRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed xUnary rUnary completeRoute
  have hausdorffUnary : UnaryHistory hausdorffRead :=
    unary_cont_closed leftUnary rightUnary hausdorffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hausdorffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
              hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                hsame row completeRead ∨ hsame row hausdorffRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle hausdorffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hausdorffRead ⟨hsame_refl hausdorffRead, hausdorffUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, hausdorffPkg⟩
  }
  exact ⟨cert, completeUnary, hausdorffUnary⟩

end BEDC.Derived.HyperspaceUp
