import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DcpoUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DcpoCarrier (O I W S M F Q L H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory W ∧ UnaryHistory S ∧
    UnaryHistory M ∧ UnaryHistory F ∧ UnaryHistory Q ∧ UnaryHistory L ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont O I W ∧ Cont M F Q

theorem DcpoCarrier_directed_supremum_handoff
    {O I W S M F Q L H C P N handoffRead completionRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont S L handoffRead →
        Cont handoffRead Q completionRead →
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                  hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                    hsame row completionRead)
              (fun row : BHist =>
                hsame row completionRead ∧
                  Cont S L handoffRead ∧ Cont handoffRead Q completionRead)
              hsame ∧
            UnaryHistory handoffRead ∧ UnaryHistory completionRead ∧
              Cont S L handoffRead ∧ Cont handoffRead Q completionRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier supremumRoute completionRoute
  obtain ⟨_oUnary, _iUnary, _wUnary, sUnary, _mUnary, _fUnary, qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed handoffUnary qUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
              hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧
              Cont S L handoffRead ∧ Cont handoffRead Q completionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionRead
          ⟨hsame_refl completionRead, completionUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro _row source
        show
          hsame _row O ∨ hsame _row I ∨ hsame _row W ∨ hsame _row S ∨
            hsame _row L ∨ hsame _row M ∨ hsame _row F ∨ hsame _row Q ∨
              hsame _row completionRead
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, supremumRoute, completionRoute⟩
    }
  exact ⟨cert, handoffUnary, completionUnary, supremumRoute, completionRoute⟩

theorem DcpoCarrier_carrier_directed_obligations
    {O I W S M F Q L H C P N directedRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont O I directedRead →
        SemanticNameCert
            (fun row : BHist => hsame row directedRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row O ∨ hsame row I ∨ hsame row W ∨
              hsame row directedRead)
            (fun row : BHist => UnaryHistory row ∧ Cont O I directedRead)
            hsame ∧
          UnaryHistory O ∧ UnaryHistory I ∧ UnaryHistory W ∧
            UnaryHistory directedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute
  obtain ⟨oUnary, iUnary, wUnary, _sUnary, _mUnary, _fUnary, _qUnary, _lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed oUnary iUnary directedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row directedRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row O ∨ hsame row I ∨ hsame row W ∨
            hsame row directedRead)
          (fun row : BHist => UnaryHistory row ∧ Cont O I directedRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro directedRead ⟨hsame_refl directedRead, directedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, directedRoute⟩
  }
  exact ⟨cert, oUnary, iUnary, wUnary, directedUnary⟩

theorem DcpoCarrier_supremum_ledger_obligations
    {O I W S M F Q L H C P N directedRead supremumRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont O I directedRead →
        Cont S L supremumRead →
          SemanticNameCert
              (fun row : BHist => hsame row supremumRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                  hsame row L ∨ hsame row supremumRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont O I directedRead ∧ Cont S L supremumRead)
              hsame ∧
            UnaryHistory directedRead ∧ UnaryHistory supremumRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute
  obtain ⟨oUnary, iUnary, _wUnary, sUnary, _mUnary, _fUnary, _qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed oUnary iUnary directedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supremumRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
              hsame row L ∨ hsame row supremumRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O I directedRead ∧ Cont S L supremumRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro supremumRead ⟨hsame_refl supremumRead, supremumUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, directedRoute, supremumRoute⟩
  }
  exact ⟨cert, directedUnary, supremumUnary⟩

theorem DcpoCarrier_continuity_scope_obligations
    {O I W S M F Q L H C P N continuityRead replayRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont S L continuityRead →
        Cont continuityRead C replayRead →
          SemanticNameCert
              (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                  hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row replayRead)
              (fun row : BHist =>
                UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
                  Cont S L continuityRead ∧ Cont continuityRead C replayRead)
              hsame ∧
            UnaryHistory continuityRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier continuityRoute replayRoute
  have carrierWitness : DcpoCarrier O I W S M F Q L H C P N := carrier
  obtain ⟨_oUnary, _iUnary, _wUnary, sUnary, _mUnary, _fUnary, _qUnary, lUnary,
    _hUnary, cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have continuityUnary : UnaryHistory continuityRead :=
    unary_cont_closed sUnary lUnary continuityRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed continuityUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
              hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
              Cont S L continuityRead ∧ Cont continuityRead C replayRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact ⟨source.right, carrierWitness, continuityRoute, replayRoute⟩
  }
  exact ⟨cert, continuityUnary, replayUnary⟩

theorem DcpoCarrier_directed_window_coverage
    {O I W S M F Q L H C P N directedRead supremumRead completionRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont O I directedRead →
        Cont directedRead W supremumRead →
          Cont S L completionRead →
            SemanticNameCert
                (fun row : BHist => (hsame row W ∨ hsame row supremumRead) ∧
                  UnaryHistory row)
                (fun row : BHist =>
                  hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                    hsame row L ∨ hsame row supremumRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont O I directedRead ∧
                    Cont directedRead W supremumRead ∧ Cont S L completionRead)
                hsame ∧ UnaryHistory directedRead ∧ UnaryHistory supremumRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute completionRoute
  obtain ⟨oUnary, iUnary, wUnary, sUnary, _mUnary, _fUnary, _qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed oUnary iUnary directedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed directedUnary wUnary supremumRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row W ∨ hsame row supremumRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
              hsame row L ∨ hsame row supremumRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O I directedRead ∧
              Cont directedRead W supremumRead ∧ Cont S L completionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro W ⟨Or.inl (hsame_refl W), wUnary⟩
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
      cases source.left with
      | inl sameWindow =>
          exact Or.inr (Or.inr (Or.inl sameWindow))
      | inr sameSupremum =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSupremum))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, directedRoute, supremumRoute, completionRoute⟩
  }
  exact ⟨cert, directedUnary, supremumUnary⟩

end BEDC.Derived.DcpoUp
