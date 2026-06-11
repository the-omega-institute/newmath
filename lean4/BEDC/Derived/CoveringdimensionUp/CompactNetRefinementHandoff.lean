import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactNetRefinementHandoff [AskSetup] [PackageSetup]
    {K E C R O L H T P N compactRead refinementRead densityRead nerveRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg ->
      Cont K E compactRead ->
        Cont compactRead R refinementRead ->
          Cont refinementRead O densityRead ->
            Cont densityRead L nerveRead ->
              Cont nerveRead N namedRead ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                          hsame row O ∨ hsame row L ∨ hsame row densityRead ∨
                            hsame row nerveRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont K E compactRead ∧
                          Cont compactRead R refinementRead ∧
                            Cont refinementRead O densityRead ∧
                              Cont densityRead L nerveRead ∧ Cont nerveRead N namedRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory compactRead ∧ UnaryHistory refinementRead ∧
                      UnaryHistory densityRead ∧ UnaryHistory nerveRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute refinementRoute densityRoute nerveRoute namedRoute namedPkg
  obtain ⟨KUnary, EUnary, _CUnary, RUnary, OUnary, LUnary, _HUnary, _TUnary,
    _PUnary, NUnary, _KEC, _CRO, _OLT, _HTP, provenancePkg, _localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed KUnary EUnary compactRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed compactUnary RUnary refinementRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed refinementUnary OUnary densityRoute
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityUnary LUnary nerveRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed nerveUnary NUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨
              hsame row L ∨ hsame row densityRead ∨ hsame row nerveRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K E compactRead ∧
              Cont compactRead R refinementRead ∧ Cont refinementRead O densityRead ∧
                Cont densityRead L nerveRead ∧ Cont nerveRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, refinementRoute, densityRoute, nerveRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, compactUnary, refinementUnary, densityUnary, nerveUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
