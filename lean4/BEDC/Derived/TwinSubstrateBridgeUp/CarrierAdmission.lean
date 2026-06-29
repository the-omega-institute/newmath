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

theorem TwinSubstrateBridgeCarrier_carrier_admission [AskSetup] [PackageSetup]
    {M G F R L H C P N metaRead groundRead frontierRead admissionRead : BHist}
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
                      Cont M G metaRead ->
                        Cont G F groundRead ->
                          Cont F R frontierRead ->
                            Cont metaRead groundRead admissionRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row admissionRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row M ∨ hsame row G ∨ hsame row F ∨
                                          hsame row R ∨ hsame row L ∨
                                            hsame row admissionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont M G metaRead ∧
                                          Cont G F groundRead ∧ Cont F R frontierRead ∧
                                            Cont metaRead groundRead admissionRead ∧
                                              PkgSig bundle P pkg ∧
                                                PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory metaRead ∧ UnaryHistory groundRead ∧
                                      UnaryHistory frontierRead ∧
                                        UnaryHistory admissionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro mUnary gUnary fUnary rUnary _lUnary _hUnary _cUnary _pUnary _nUnary metaRoute
    groundRoute frontierRoute admissionRoute provenancePkg namePkg
  have metaUnary : UnaryHistory metaRead :=
    unary_cont_closed mUnary gUnary metaRoute
  have groundUnary : UnaryHistory groundRead :=
    unary_cont_closed gUnary fUnary groundRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed fUnary rUnary frontierRoute
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed metaUnary groundUnary admissionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admissionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row G ∨ hsame row F ∨ hsame row R ∨ hsame row L ∨
              hsame row admissionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M G metaRead ∧ Cont G F groundRead ∧
              Cont F R frontierRead ∧ Cont metaRead groundRead admissionRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro admissionRead ⟨hsame_refl admissionRead, admissionUnary⟩
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
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metaRoute, groundRoute, frontierRoute, admissionRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, metaUnary, groundUnary, frontierUnary, admissionUnary⟩

end BEDC.Derived.TwinSubstrateBridgeUp
