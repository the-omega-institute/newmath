import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionLeftExactness_carrier_admission [AskSetup] [PackageSetup]
    {S U D K E H C P N sourceUnit denseKernel admissionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionLeftExactnessCarrier S U D K E H C P N ->
      Cont S U sourceUnit ->
        Cont D K denseKernel ->
          Cont sourceUnit denseKernel admissionRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row admissionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row K ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row sourceUnit ∨ hsame row denseKernel ∨
                            hsame row admissionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S U sourceUnit ∧
                        Cont D K denseKernel ∧ Cont sourceUnit denseKernel admissionRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory sourceUnit ∧ UnaryHistory denseKernel ∧
                    UnaryHistory admissionRead := by
  -- BEDC touchpoint anchor: CauchyCompletionLeftExactnessCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceUnitRoute denseKernelRoute admissionRoute provenancePkg namePkg
  obtain ⟨sUnary, uUnary, dUnary, kUnary, _eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary⟩ := carrier
  have sourceUnitUnary : UnaryHistory sourceUnit :=
    unary_cont_closed sUnary uUnary sourceUnitRoute
  have denseKernelUnary : UnaryHistory denseKernel :=
    unary_cont_closed dUnary kUnary denseKernelRoute
  have admissionReadUnary : UnaryHistory admissionRead :=
    unary_cont_closed sourceUnitUnary denseKernelUnary admissionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admissionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row K ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sourceUnit ∨ hsame row denseKernel ∨
                  hsame row admissionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U sourceUnit ∧ Cont D K denseKernel ∧
              Cont sourceUnit denseKernel admissionRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro admissionRead ⟨hsame_refl admissionRead, admissionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceUnitRoute, denseKernelRoute, admissionRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, sourceUnitUnary, denseKernelUnary, admissionReadUnary⟩

end BEDC.Derived.CauchyUp
