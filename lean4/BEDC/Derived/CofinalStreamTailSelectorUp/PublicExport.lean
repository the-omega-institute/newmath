import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorCarrier_public_export [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N windowRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont epsilon W windowRead →
        Cont W R sealRead →
          Cont sealRead A publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                      hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row windowRead ∨
                          hsame row sealRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont epsilon W windowRead ∧ Cont W R sealRead ∧
                      Cont sealRead A publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier windowRoute sealRoute publicRoute publicPkg
  obtain ⟨epsilonUnary, wUnary, rUnary, _dUnary, aUnary, _sigmaUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed epsilonUnary wUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed wUnary rUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary aUnary publicRoute
  refine ⟨?_, windowUnary, sealUnary, publicUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨publicRead, hsame_refl publicRead, publicUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left)))))))))))
  · intro _row sourceRow
    exact ⟨sourceRow.right, windowRoute, sealRoute, publicRoute, publicPkg⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
