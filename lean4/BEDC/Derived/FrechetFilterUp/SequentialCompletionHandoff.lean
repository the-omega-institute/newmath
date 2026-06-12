import BEDC.Derived.FrechetFilterUp

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterSequentialCompletionHandoff [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N tailRead cauchyRead readbackRead sealRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T tailRead ->
        Cont tailRead Q cauchyRead ->
          Cont cauchyRead R readbackRead ->
            Cont readbackRead A sealRead ->
              Cont sealRead N completionRead ->
                PkgSig bundle P pkg ->
                  PkgSig bundle completionRead pkg ->
                    SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨
                          hsame row A ∨ hsame row completionRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont U T tailRead ∧
                          Cont tailRead Q cauchyRead ∧ Cont cauchyRead R readbackRead ∧
                            Cont readbackRead A sealRead ∧
                              Cont sealRead N completionRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle completionRead pkg)
                      hsame ∧
                    UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute cauchyRoute readbackRoute sealRoute completionRoute provenancePkg
    completionPkg
  obtain ⟨UUnary, TUnary, _SUnary, _MUnary, _BUnary, QUnary, RUnary, AUnary,
    _HUnary, _CUnary, _PUnary, NUnary, _carrierTailRoute, _carrierScheduleRoute,
    _carrierCauchyRoute, _carrierSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ :=
      carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed UUnary TUnary tailRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed tailUnary QUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary RUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary AUnary sealRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary NUnary completionRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row U ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨ hsame row A ∨
            hsame row completionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont U T tailRead ∧ Cont tailRead Q cauchyRead ∧
            Cont cauchyRead R readbackRead ∧ Cont readbackRead A sealRead ∧
              Cont sealRead N completionRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle completionRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, tailRoute, cauchyRoute, readbackRoute, sealRoute,
          completionRoute, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, completionUnary⟩

end BEDC.Derived.FrechetFilterUp
