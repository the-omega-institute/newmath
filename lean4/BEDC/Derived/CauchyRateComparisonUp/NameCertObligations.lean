import BEDC.Derived.CauchyRateComparisonUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyRateComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyRateComparisonCarrier [AskSetup] [PackageSetup]
    (R0 R1 W D Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory R0 ∧ UnaryHistory R1 ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyRateComparisonNameCertObligations [AskSetup] [PackageSetup]
    {R0 R1 W D Q E H C P N windowRead toleranceRead comparisonRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateComparisonCarrier R0 R1 W D Q E H C P N bundle pkg ->
      Cont R0 W windowRead -> Cont R1 W toleranceRead ->
        Cont windowRead D comparisonRead -> Cont comparisonRead E sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row R0 ∨ hsame row R1 ∨ hsame row W ∨ hsame row D ∨
                    hsame row Q ∨ hsame row E ∨ hsame row windowRead ∨
                      hsame row toleranceRead ∨ hsame row comparisonRead ∨
                        hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont R0 W windowRead ∧
                    Cont R1 W toleranceRead ∧ Cont windowRead D comparisonRead ∧
                      Cont comparisonRead E sealRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier windowRoute toleranceRoute comparisonRoute sealRoute sealPkg
  obtain ⟨r0Unary, r1Unary, wUnary, dUnary, _qUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg, namePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed r0Unary wUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed r1Unary wUnary toleranceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary dUnary comparisonRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed comparisonUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row R1 ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨
              hsame row E ∨ hsame row windowRead ∨ hsame row toleranceRead ∨
                hsame row comparisonRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R0 W windowRead ∧ Cont R1 W toleranceRead ∧
              Cont windowRead D comparisonRead ∧ Cont comparisonRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, comparisonRoute, sealRoute,
          provenancePkg, namePkg, sealPkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, comparisonUnary, sealUnary⟩

end BEDC.Derived.CauchyRateComparisonUp
