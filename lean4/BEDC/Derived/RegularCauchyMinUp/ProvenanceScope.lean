import BEDC.Derived.RegularCauchyMinUp.CarrierAdmission
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_provenance_scope [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N ->
      PkgSig bundle P pkg ->
        PkgSig bundle N pkg ->
          SemanticNameCert
              (fun row : BHist => (hsame row P ∨ hsame row N) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                  hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                    hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory P ∧ UnaryHistory N := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier provenancePkg namePkg
  obtain ⟨_aUnary, _bUnary, _wUnary, _daUnary, _dbUnary, _jUnary, _sUnary, _rUnary,
    _eUnary, _hUnary, _cUnary, pUnary, nUnary⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row P ∨ hsame row N) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro P ⟨Or.inl (hsame_refl P), pUnary⟩
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
        intro row other sameRows source
        have lift : ∀ {target : BHist}, hsame row target -> hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl sameP =>
              exact Or.inl (lift sameP)
          | inr sameN =>
              exact Or.inr (lift sameN)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameP =>
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
                                  (Or.inl sameP)))))))))))
      | inr sameN =>
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
                                  (Or.inr sameN)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, pUnary, nUnary⟩

end BEDC.Derived.RegularCauchyMinUp
