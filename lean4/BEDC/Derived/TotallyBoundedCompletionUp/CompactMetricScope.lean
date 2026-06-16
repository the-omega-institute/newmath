import BEDC.Derived.TotallyBoundedCompletionUp

namespace BEDC.Derived.TotallyBoundedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotallyBoundedCompletionCarrier_compact_metric_scope [AskSetup] [PackageSetup]
    {X T N F E C S U H P L compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TotallyBoundedCompletionCarrier X T N F E C S U H P L bundle pkg ->
      Cont T N F ->
        Cont F E C ->
          Cont C U compactRead ->
            PkgSig bundle compactRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row N ∨ hsame row F ∨ hsame row E ∨
                      hsame row C ∨ hsame row S ∨ hsame row U ∨ hsame row H ∨
                        hsame row P ∨ hsame row L ∨ hsame row compactRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont T N F ∧ Cont F E C ∧
                      Cont C U compactRead ∧ PkgSig bundle compactRead pkg)
                  hsame ∧
                UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier finiteNetRoute completionRoute compactRoute compactPkg
  obtain ⟨xUnary, tUnary, fUnary, cUnary, uUnary, _hUnary, xTnRoute,
    nFeRoute, _eCsRoute, _sUpRoute, _hPlRoute, _pPkg, _lPkg⟩ := carrier
  have nUnary : UnaryHistory N :=
    unary_cont_closed (h := X) (k := T) (r := N) xUnary tUnary xTnRoute
  have eUnary : UnaryHistory E :=
    unary_cont_closed (h := N) (k := F) (r := E) nUnary fUnary nFeRoute
  have _cUnaryFromRoute : UnaryHistory C :=
    unary_cont_closed (h := F) (k := E) (r := C) fUnary eUnary completionRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed (h := C) (k := U) (r := compactRead) cUnary uUnary compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row N ∨ hsame row F ∨ hsame row E ∨
              hsame row C ∨ hsame row S ∨ hsame row U ∨ hsame row H ∨
                hsame row P ∨ hsame row L ∨ hsame row compactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T N F ∧ Cont F E C ∧
              Cont C U compactRead ∧ PkgSig bundle compactRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, finiteNetRoute, completionRoute, compactRoute, compactPkg⟩
  }
  exact ⟨cert, compactUnary⟩

end BEDC.Derived.TotallyBoundedCompletionUp
