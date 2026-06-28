import BEDC.Derived.RegularCauchyMinUp.SelectorTransportStability
import BEDC.FKernel.Package

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyMinCarrier (A B W DA DB J S R E H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory DA ∧
    UnaryHistory DB ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory R ∧
      UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N

theorem RegularCauchyMinCarrier_admission_obligation [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N selectedRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory W ->
          UnaryHistory DA ->
            UnaryHistory DB ->
              UnaryHistory S ->
                UnaryHistory R ->
                  UnaryHistory E ->
                    Cont A W selectedRead ->
                      Cont selectedRead DA S ->
                        Cont S R readbackRead ->
                          Cont readbackRead E sealRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row S ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row A ∨ hsame row B ∨ hsame row W ∨
                                        hsame row DA ∨ hsame row DB ∨ hsame row J ∨
                                          hsame row S ∨ hsame row R ∨ hsame row E ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row N)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont A W selectedRead ∧
                                        Cont selectedRead DA S ∧ Cont S R readbackRead ∧
                                          Cont readbackRead E sealRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory selectedRead ∧ UnaryHistory readbackRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro aUnary _bUnary wUnary daUnary _dbUnary sUnary rUnary eUnary selectedRoute
    selectedCommit readbackRoute sealRoute pPkg nPkg
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed aUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed sUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row S ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
              hsame row J ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A W selectedRead ∧ Cont selectedRead DA S ∧
              Cont S R readbackRead ∧ Cont readbackRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro S ⟨hsame_refl S, sUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedRoute, selectedCommit, readbackRoute, sealRoute,
          pPkg, nPkg⟩
  }
  exact ⟨cert, selectedUnary, readbackUnary, sealUnary⟩

theorem RegularCauchyMinCarrier_namecert_obligations
    {A B W DA DB J S R E H C P N selectorRead sealRead : BHist} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N ->
      Cont J S selectorRead ->
        Cont R E sealRead ->
          SemanticNameCert
              (fun row : BHist =>
                (hsame row selectorRead ∨ hsame row sealRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                  hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                    hsame row E ∨ hsame row selectorRead ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont J S selectorRead ∧ Cont R E sealRead)
              hsame ∧
            UnaryHistory selectorRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute sealRoute
  obtain ⟨_aUnary, _bUnary, _wUnary, _daUnary, _dbUnary, jUnary, sUnary, rUnary,
    eUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed jUnary sUnary selectorRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row selectorRead ∨ hsame row sealRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row selectorRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J S selectorRead ∧ Cont R E sealRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro selectorRead ⟨Or.inl (hsame_refl selectorRead), selectorUnary⟩
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
        constructor
        · cases source.left with
          | inl sameSelector =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSelector)
          | inr sameSeal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSelector =>
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
                              (Or.inl sameSelector)))))))))
      | inr sameSeal =>
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
                              (Or.inr sameSeal)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, selectorRoute, sealRoute⟩
  }
  exact ⟨cert, selectorUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyMinUp
