import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceCarrier_bolzano_source_exactness [AskSetup] [PackageSetup]
    {S W Q R I H C P N windowRead readbackRead sealRead boundRead bolzanoRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg ->
      Cont S W windowRead ->
        Cont windowRead Q readbackRead ->
          Cont readbackRead R sealRead ->
            Cont sealRead I boundRead ->
              Cont boundRead H bolzanoRead ->
                PkgSig bundle bolzanoRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row bolzanoRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
                          hsame row I ∨ Cont boundRead H bolzanoRead)
                      (fun row : BHist =>
                        PkgSig bundle P pkg ∧ PkgSig bundle bolzanoRead pkg ∧
                          hsame row bolzanoRead)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory boundRead ∧
                        UnaryHistory bolzanoRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute readbackRoute sealRoute boundRoute bolzanoRoute bolzanoPkg
  obtain ⟨sUnary, wUnary, qUnary, rUnary, iUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _intervalRoute, _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary rUnary sealRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed sealUnary iUnary boundRoute
  have bolzanoUnary : UnaryHistory bolzanoRead :=
    unary_cont_closed boundUnary hUnary bolzanoRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bolzanoRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
              hsame row I ∨ Cont boundRead H bolzanoRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle bolzanoRead pkg ∧
              hsame row bolzanoRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro bolzanoRead ⟨hsame_refl bolzanoRead, bolzanoUnary⟩
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
        intro _row _sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr bolzanoRoute))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨provenancePkg, bolzanoPkg, sourceRow.left⟩
    }
  exact
    ⟨cert, windowUnary, readbackUnary, sealUnary, boundUnary, bolzanoUnary⟩

end BEDC.Derived.BoundedRealSequenceUp
