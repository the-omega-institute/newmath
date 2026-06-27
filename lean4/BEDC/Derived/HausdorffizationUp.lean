import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def HausdorffizationCarrier (P S M C W R E T K G N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory P ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory C ∧
    UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory T ∧
      UnaryHistory K ∧ UnaryHistory G ∧ UnaryHistory N ∧ Cont P S M ∧ Cont M C K

theorem HausdorffizationCarrier_completion_consumer_route
    {P S M C W R E T K G N completionRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont M C completionRead →
        SemanticNameCert
            (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                hsame row completionRead)
            (fun row : BHist =>
              UnaryHistory row ∧
                HausdorffizationCarrier P S M C W R E T K G N ∧ Cont M C completionRead)
            hsame ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData completionRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨_pUnary, _sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              HausdorffizationCarrier P S M C W R E T K G N ∧ Cont M C completionRead)
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, completionRoute⟩
  }
  exact ⟨cert, completionUnary⟩

theorem HausdorffizationCarrier_separated_reflection
    {P S M C W R E T K G N separatedRead completionRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S separatedRead →
        Cont separatedRead M completionRead →
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
                  hsame row R ∨ hsame row E ∨ hsame row completionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont P S separatedRead ∧
                  Cont separatedRead M completionRead)
              hsame ∧ UnaryHistory separatedRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData separatedRoute completionRoute
  obtain ⟨pUnary, sUnary, mUnary, _cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed pUnary sUnary separatedRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary mUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P S separatedRead ∧
              Cont separatedRead M completionRead)
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, separatedRoute, completionRoute⟩
  }
  exact ⟨cert, separatedUnary, completionUnary⟩

theorem HausdorffizationCarrier_ledger_nonquotient_boundary
    {P S M C W R E T K G N ledgerRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont S W ledgerRead →
        SemanticNameCert
            (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row P ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                hsame row E ∨ hsame row ledgerRead)
            (fun row : BHist =>
              UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                Cont S W ledgerRead)
            hsame ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData ledgerRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨_pUnary, sUnary, _mUnary, _cUnary, wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sUnary wUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont S W ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact ⟨sourceRow.right, carrierOriginal, ledgerRoute⟩
  }
  exact ⟨cert, ledgerUnary⟩

theorem HausdorffizationCarrier_separated_reflection_scope
    {P S M C W R E T K G N boundaryRead windowRead sealRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont boundaryRead W windowRead →
          Cont windowRead E sealRead →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row P ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                    hsame row E ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont P S boundaryRead ∧
                    Cont boundaryRead W windowRead ∧ Cont windowRead E sealRead)
                hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory windowRead ∧
              UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute windowRoute sealRoute
  obtain ⟨pUnary, sUnary, _mUnary, _cUnary, wUnary, _rUnary, eUnary, _tUnary,
    _kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed boundaryUnary wUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P S boundaryRead ∧
              Cont boundaryRead W windowRead ∧ Cont windowRead E sealRead)
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
      exact ⟨sourceRow.right, boundaryRoute, windowRoute, sealRoute⟩
  }
  exact ⟨cert, boundaryUnary, windowUnary, sealUnary⟩

theorem HausdorffizationCompletionRouteStability
    {P S M C W R E T K G N completionRead replayRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont M C completionRead →
        Cont completionRead K replayRead →
          SemanticNameCert
              (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row T ∨
                  hsame row K ∨ hsame row replayRead)
              (fun row : BHist =>
                UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                  Cont M C completionRead ∧ Cont completionRead K replayRead)
              hsame ∧
            UnaryHistory completionRead ∧
              UnaryHistory replayRead ∧ hsame replayRead (append completionRead K) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory append
  intro carrierData completionRoute replayRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨_pUnary, _sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary kUnary replayRoute
  have replayExact : hsame replayRead (append completionRead K) := by
    cases replayRoute
    exact hsame_refl _
  have replaySource :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row T ∨
              hsame row K ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont M C completionRead ∧ Cont completionRead K replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead replaySource
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, completionRoute, replayRoute⟩
  }
  exact ⟨cert, completionUnary, replayUnary, replayExact⟩

theorem HausdorffizationCarrier_completion_handoff_exactness
    {P S M C W R E T K G N boundaryRead completionRead handoffRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont P S boundaryRead →
        Cont M C completionRead →
          Cont completionRead N handoffRead →
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
                    hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                      hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont P S boundaryRead ∧
                    Cont M C completionRead ∧ Cont completionRead N handoffRead)
                hsame ∧ UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData boundaryRoute completionRoute handoffRoute
  obtain ⟨pUnary, sUnary, mUnary, cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, _gUnary, nUnary, _sourceRoute, _handoffCarrierRoute⟩ := carrierData
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed pUnary sUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary cUnary completionRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary nUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                hsame row K ∨ hsame row G ∨ hsame row N ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P S boundaryRead ∧
              Cont M C completionRead ∧ Cont completionRead N handoffRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, boundaryRoute, completionRoute, handoffRoute⟩
  }
  exact ⟨cert, boundaryUnary, completionUnary, handoffUnary⟩

theorem HausdorffizationZeroDistanceExactness
    {P S M C W R E _T _K _G _N boundaryRead completionRead realRead : BHist} :
    Cont P S boundaryRead →
      Cont W R realRead →
        Cont M C completionRead →
          SemanticNameCert
            (fun row : BHist => hsame row S ∨ hsame row boundaryRead)
            (fun row : BHist =>
              hsame row P ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                hsame row boundaryRead ∨ hsame row realRead)
            (fun row : BHist =>
              (hsame row S ∨ hsame row boundaryRead) ∧ Cont P S boundaryRead ∧
                Cont W R realRead ∧ Cont M C completionRead)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert NameCert
  intro boundaryRoute realRoute completionRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro S (Or.inl (hsame_refl S))
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
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        cases source with
        | inl sameS =>
            exact Or.inl (lift sameS)
        | inr sameBoundary =>
            exact Or.inr (lift sameBoundary)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameS =>
          exact Or.inr (Or.inl sameS)
      | inr sameBoundary =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBoundary)))))
    ledger_sound := by
      intro _row source
      exact ⟨source, boundaryRoute, realRoute, completionRoute⟩
  }

end HausdorffizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def HausdorffizationUp : Prop :=
  True

theorem HausdorffizationCarrier_namecert_obligations (P S M C W R E T K G N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
          hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
            hsame row N)
      (fun row : BHist =>
        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
          hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
            hsame row N)
      (fun row : BHist =>
        hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
          hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
            hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro P (Or.inl (hsame_refl P))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem HausdorffizationCarrier_separated_reflection_boundary
    {P S M C W R E T K G N boundaryRead completionRead : BHist} :
    Cont P S boundaryRead →
      Cont M C completionRead →
        SemanticNameCert
          (fun row : BHist => hsame row S ∨ hsame row boundaryRead)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row boundaryRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            (hsame row S ∨ hsame row boundaryRead) ∧ Cont P S boundaryRead ∧
              Cont M C completionRead)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert NameCert
  intro hBoundary hCompletion
  exact {
    core := {
      carrier_inhabited := Exists.intro S (Or.inl (hsame_refl S))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameS =>
          exact Or.inr (Or.inl sameS)
      | inr sameBoundary =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBoundary)))))))
    ledger_sound := by
      intro row source
      exact And.intro source (And.intro hBoundary hCompletion)
  }

end BEDC.Derived
