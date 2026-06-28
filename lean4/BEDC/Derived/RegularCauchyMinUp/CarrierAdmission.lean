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

theorem RegularCauchyMinSelector_stability_scope
    {A B W DA DB J S R E H C P N leftWindow rightWindow leftLedger rightLedger
      selectedRead readbackRead sealRead transportRead replayRead : BHist} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N →
      Cont A W leftWindow →
        Cont B W rightWindow →
          Cont leftWindow DA leftLedger →
            Cont rightWindow DB rightLedger →
              Cont J S selectedRead →
                Cont selectedRead R readbackRead →
                  Cont readbackRead E sealRead →
                    Cont sealRead H transportRead →
                      Cont transportRead C replayRead →
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row replayRead ∨ hsame row leftLedger ∨
                                  hsame row rightLedger) ∧
                                UnaryHistory row)
                            (fun row : BHist =>
                              hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                                hsame row DB ∨ hsame row J ∨ hsame row S ∨
                                  hsame row R ∨ hsame row E ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                      hsame row leftLedger ∨ hsame row rightLedger ∨
                                        hsame row replayRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
                                  Cont A W leftWindow ∧ Cont B W rightWindow ∧
                                    Cont leftWindow DA leftLedger ∧
                                      Cont rightWindow DB rightLedger ∧
                                        Cont J S selectedRead ∧
                                          Cont selectedRead R readbackRead ∧
                                            Cont readbackRead E sealRead ∧
                                              Cont sealRead H transportRead ∧
                                                Cont transportRead C replayRead)
                            hsame ∧ UnaryHistory leftLedger ∧ UnaryHistory rightLedger ∧
                          UnaryHistory selectedRead ∧ UnaryHistory readbackRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory transportRead ∧
                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData leftWindowRoute rightWindowRoute leftLedgerRoute rightLedgerRoute
    selectedRoute readbackRoute sealRoute transportRoute replayRoute
  have carrierOriginal : RegularCauchyMinCarrier A B W DA DB J S R E H C P N :=
    carrierData
  obtain ⟨aUnary, bUnary, wUnary, daUnary, dbUnary, jUnary, sUnary, rUnary,
    eUnary, hUnary, cUnary, _pUnary, _nUnary⟩ := carrierData
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed aUnary wUnary leftWindowRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed bUnary wUnary rightWindowRoute
  have leftLedgerUnary : UnaryHistory leftLedger :=
    unary_cont_closed leftWindowUnary daUnary leftLedgerRoute
  have rightLedgerUnary : UnaryHistory rightLedger :=
    unary_cont_closed rightWindowUnary dbUnary rightLedgerRoute
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed jUnary sUnary selectedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectedUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row replayRead ∨ hsame row leftLedger ∨ hsame row rightLedger) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
              hsame row J ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row leftLedger ∨
                  hsame row rightLedger ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
              Cont A W leftWindow ∧ Cont B W rightWindow ∧
                Cont leftWindow DA leftLedger ∧ Cont rightWindow DB rightLedger ∧
                  Cont J S selectedRead ∧ Cont selectedRead R readbackRead ∧
                    Cont readbackRead E sealRead ∧ Cont sealRead H transportRead ∧
                      Cont transportRead C replayRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨Or.inl (hsame_refl replayRead), replayUnary⟩
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
        intro row other sameRows sourceRow
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameReplay =>
              exact Or.inl (lift sameReplay)
          | inr rest =>
              cases rest with
              | inl sameLeftLedger =>
                  exact Or.inr (Or.inl (lift sameLeftLedger))
              | inr sameRightLedger =>
                  exact Or.inr (Or.inr (lift sameRightLedger))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameReplay =>
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
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr sameReplay))))))))))))))
      | inr rest =>
          cases rest with
          | inl sameLeftLedger =>
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
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl sameLeftLedger)))))))))))))
          | inr sameRightLedger =>
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
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl sameRightLedger))))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, leftWindowRoute, rightWindowRoute,
          leftLedgerRoute, rightLedgerRoute, selectedRoute, readbackRoute, sealRoute,
          transportRoute, replayRoute⟩
  }
  exact
    ⟨cert, leftLedgerUnary, rightLedgerUnary, selectedUnary, readbackUnary, sealUnary,
      transportUnary, replayUnary⟩

theorem RegularCauchyMinCarrier_shared_window_scope
    {A B W DA DB J S R E H C P N selectorRead readbackRead sealRead : BHist} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N →
      Cont W DA selectorRead →
        Cont selectorRead R readbackRead →
          Cont readbackRead E sealRead →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                    hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                      hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
                    Cont W DA selectorRead ∧ Cont selectorRead R readbackRead ∧
                      Cont readbackRead E sealRead)
                hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory readbackRead ∧
              UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute readbackRoute sealRoute
  have carrierOriginal : RegularCauchyMinCarrier A B W DA DB J S R E H C P N := carrier
  obtain ⟨_aUnary, _bUnary, wUnary, daUnary, _dbUnary, _jUnary, _sUnary, rUnary,
    eUnary, _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed wUnary daUnary selectorRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectorUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
              Cont W DA selectorRead ∧ Cont selectorRead R readbackRead ∧
                Cont readbackRead E sealRead)
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
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carrierOriginal, selectorRoute, readbackRoute, sealRoute⟩
  }
  exact ⟨cert, selectorUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyMinUp
