import BEDC.Derived.CauchyOscillationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationDyadicTailRealSealRoute [AskSetup] [PackageSetup]
    {W M Q T S H C P N windowRead toleranceRead ledgerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg →
      Cont W M windowRead →
        Cont windowRead Q toleranceRead →
          Cont toleranceRead T ledgerRead →
            Cont ledgerRead S sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                        hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row windowRead ∨
                            hsame row toleranceRead ∨ hsame row ledgerRead ∨
                              hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W M windowRead ∧
                        Cont windowRead Q toleranceRead ∧
                          Cont toleranceRead T ledgerRead ∧
                            Cont ledgerRead S sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier windowRoute toleranceRoute ledgerRoute sealRoute sealPkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _tailWindowModulus, _modulusTolerance, _ledgerSeal, _routesNameCert,
    _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary mUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary qUnary toleranceRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed toleranceUnary tUnary ledgerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row windowRead ∨ hsame row toleranceRead ∨ hsame row ledgerRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M windowRead ∧ Cont windowRead Q toleranceRead ∧
              Cont toleranceRead T ledgerRead ∧ Cont ledgerRead S sealRead ∧
                PkgSig bundle sealRead pkg)
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, toleranceRoute, ledgerRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, ledgerUnary, sealUnary⟩

end BEDC.Derived.CauchyOscillationUp
