import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricTailCofinality [AskSetup] [PackageSetup]
    {X S M L D H C P N tailRead cofinalWindow limitRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentiallyCompleteMetricCarrier X S M L D H C P N bundle pkg →
      Cont S M tailRead →
        Cont tailRead D cofinalWindow →
          Cont cofinalWindow L limitRead →
            Cont limitRead N completionRead →
              PkgSig bundle N pkg →
                PkgSig bundle completionRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row M ∨ hsame row D ∨ hsame row L ∨
                          hsame row tailRead ∨ hsame row cofinalWindow ∨
                            hsame row limitRead ∨ hsame row completionRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S M tailRead ∧
                          Cont tailRead D cofinalWindow ∧
                            Cont cofinalWindow L limitRead ∧
                              Cont limitRead N completionRead ∧ PkgSig bundle N pkg ∧
                                PkgSig bundle completionRead pkg)
                      hsame ∧
                    UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute cofinalRoute limitRoute completionRoute namePkg completionPkg
  obtain ⟨_xUnary, sUnary, mUnary, lUnary, dUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _sourceStreamRoute, _routeLimitLedger, _transportName, _provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sUnary mUnary tailRoute
  have cofinalUnary : UnaryHistory cofinalWindow :=
    unary_cont_closed tailUnary dUnary cofinalRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed cofinalUnary lUnary limitRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed limitUnary nUnary completionRoute
  constructor
  · exact {
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
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, tailRoute, cofinalRoute, limitRoute, completionRoute, namePkg,
            completionPkg⟩
    }
  · exact completionUnary

end BEDC.Derived.SequentiallyCompleteMetricUp
