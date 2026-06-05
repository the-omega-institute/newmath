import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalModulusConsumption [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg →
      Cont S M modulusRead →
        Cont modulusRead Q selectorRead →
          Cont selectorRead F fastRead →
            Cont fastRead R regularRead →
              Cont regularRead W tailRead →
                PkgSig bundle tailRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
                          hsame row W ∨ hsame row tailRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S M modulusRead ∧
                          Cont modulusRead Q selectorRead ∧ Cont selectorRead F fastRead ∧
                            Cont fastRead R regularRead ∧ Cont regularRead W tailRead ∧
                              PkgSig bundle tailRead pkg ∧ PkgSig bundle P pkg)
                      hsame ∧ UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                    UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory tailRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier modulusRoute selectorRoute fastRoute regularRoute tailRoute tailPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed regularUnary unaryW tailRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M modulusRead ∧ Cont modulusRead Q selectorRead ∧
              Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                Cont regularRead W tailRead ∧ PkgSig bundle tailRead pkg ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
        ⟨sourceRow.right, modulusRoute, selectorRoute, fastRoute, regularRoute,
          tailRoute, tailPkg, provenancePkg⟩
  }
  exact
    ⟨cert, modulusUnary, selectorUnary, fastUnary, regularUnary, tailUnary,
      provenancePkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
