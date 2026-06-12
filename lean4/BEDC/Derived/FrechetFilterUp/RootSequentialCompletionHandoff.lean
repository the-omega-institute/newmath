import BEDC.Derived.FrechetFilterUp

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterRootSequentialCompletionHandoff [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N tailRead scheduleRead filterRead cauchyRead readbackRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T tailRead ->
        Cont tailRead S scheduleRead ->
          Cont scheduleRead B filterRead ->
            Cont filterRead Q cauchyRead ->
              Cont cauchyRead R readbackRead ->
                Cont readbackRead A sealRead ->
                  Cont sealRead N namedRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle namedRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
                                hsame row B ∨ hsame row Q ∨ hsame row R ∨
                                  hsame row A ∨ hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont U T tailRead ∧
                                Cont tailRead S scheduleRead ∧
                                  Cont scheduleRead B filterRead ∧
                                    Cont filterRead Q cauchyRead ∧
                                      Cont cauchyRead R readbackRead ∧
                                        Cont readbackRead A sealRead ∧
                                          Cont sealRead N namedRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle namedRead pkg)
                            hsame ∧
                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute scheduleRoute filterRoute cauchyRoute readbackRoute sealRoute
    namedRoute provenancePkg namedPkg
  obtain ⟨uUnary, tUnary, sUnary, _mUnary, bUnary, qUnary, rUnary, aUnary, _hUnary,
    _cUnary, _pUnary, nUnary, _carrierTail, _carrierSchedule, _carrierReadback,
    _carrierSeal, _carrierProvenance, _carrierName⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed uUnary tUnary tailRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed tailUnary sUnary scheduleRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed scheduleUnary bUnary filterRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed filterUnary qUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  constructor
  · exact {
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, tailRoute, scheduleRoute, filterRoute, cauchyRoute,
            readbackRoute, sealRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact namedUnary

end BEDC.Derived.FrechetFilterUp
