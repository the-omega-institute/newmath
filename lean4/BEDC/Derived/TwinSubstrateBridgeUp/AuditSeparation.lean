import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TwinSubstrateBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TwinSubstrateBridgeCarrier_audit_separation [AskSetup] [PackageSetup]
    {M G F R L H C P N metaRead groundRead frontierRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory G ->
        UnaryHistory F ->
          UnaryHistory R ->
            UnaryHistory L ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont M R metaRead ->
                        Cont G R groundRead ->
                          Cont F L frontierRead ->
                            Cont metaRead frontierRead bridgeRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row bridgeRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row G ∨ hsame row F ∨
                                          hsame row R ∨ hsame row L ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row metaRead ∨ hsame row groundRead ∨
                                                hsame row frontierRead ∨ hsame row bridgeRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont M R metaRead ∧
                                          Cont G R groundRead ∧ Cont F L frontierRead ∧
                                            Cont metaRead frontierRead bridgeRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory metaRead ∧ UnaryHistory groundRead ∧
                                      UnaryHistory frontierRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro mUnary gUnary fUnary rUnary lUnary _hUnary _cUnary _pUnary _nUnary
    metaRoute groundRoute frontierRoute bridgeRoute provenancePkg namePkg
  have metaUnary : UnaryHistory metaRead :=
    unary_cont_closed mUnary rUnary metaRoute
  have groundUnary : UnaryHistory groundRead :=
    unary_cont_closed gUnary rUnary groundRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed fUnary lUnary frontierRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed metaUnary frontierUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row F ∨ hsame row R ∨ hsame row L ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row metaRead ∨ hsame row groundRead ∨ hsame row frontierRead ∨
                  hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R metaRead ∧ Cont G R groundRead ∧
              Cont F L frontierRead ∧ Cont metaRead frontierRead bridgeRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metaRoute, groundRoute, frontierRoute, bridgeRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, metaUnary, groundUnary, frontierUnary, bridgeUnary⟩

end BEDC.Derived.TwinSubstrateBridgeUp
