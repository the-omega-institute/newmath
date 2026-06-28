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

theorem DcpoCarrier_lower_bound_exactness
    {O I W S M F Q L H C P N directedRead supremumRead exactnessRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N ->
      Cont O I directedRead ->
        Cont S L supremumRead ->
          Cont supremumRead L exactnessRead ->
            SemanticNameCert
                (fun row : BHist => hsame row exactnessRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                    hsame row L ∨ hsame row exactnessRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
                    Cont O I directedRead ∧ Cont S L supremumRead ∧
                      Cont supremumRead L exactnessRead)
                hsame ∧
              UnaryHistory exactnessRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute exactnessRoute
  have carrierWitness : DcpoCarrier O I W S M F Q L H C P N := carrier
  obtain ⟨_oUnary, _iUnary, _wUnary, sUnary, _mUnary, _fUnary, _qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have exactnessUnary : UnaryHistory exactnessRead :=
    unary_cont_closed supremumUnary lUnary exactnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
              hsame row L ∨ hsame row exactnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
              Cont O I directedRead ∧ Cont S L supremumRead ∧
                Cont supremumRead L exactnessRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exactnessRead ⟨hsame_refl exactnessRead, exactnessUnary⟩
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
      exact
        ⟨source.right, carrierWitness, directedRoute, supremumRoute, exactnessRoute⟩
  }
  exact ⟨cert, exactnessUnary⟩

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

private theorem DcpoCarrier_directed_window_coverage_unary_route
    {O I W S M F Q L H C P N directedRead supremumRead handoffRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N ->
      Cont O I directedRead ->
        Cont S L supremumRead ->
          Cont supremumRead Q handoffRead ->
            UnaryHistory W ∧ UnaryHistory directedRead ∧ UnaryHistory supremumRead ∧
              UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier directedRoute supremumRoute handoffRoute
  obtain ⟨oUnary, iUnary, wUnary, sUnary, _mUnary, _fUnary, qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed oUnary iUnary directedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed supremumUnary qUnary handoffRoute
  exact ⟨wUnary, directedUnary, supremumUnary, handoffUnary⟩

theorem DcpoCarrier_directed_window_coverage
    {O I W S M F Q L H C P N directedRead supremumRead handoffRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N ->
      Cont O I directedRead ->
        Cont S L supremumRead ->
          Cont supremumRead Q handoffRead ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row W ∨ hsame row directedRead ∨ hsame row supremumRead ∨
                      hsame row handoffRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                    hsame row L ∨ hsame row Q ∨ hsame row directedRead ∨
                      hsame row supremumRead ∨ hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont O I directedRead ∧ Cont S L supremumRead ∧
                    Cont supremumRead Q handoffRead)
                hsame ∧
              UnaryHistory W ∧ UnaryHistory directedRead ∧ UnaryHistory supremumRead ∧
                UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute handoffRoute
  have unaryRoute :=
    DcpoCarrier_directed_window_coverage_unary_route
      carrier directedRoute supremumRoute handoffRoute
  obtain ⟨wUnary, directedUnary, supremumUnary, handoffUnary⟩ := unaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row W ∨ hsame row directedRead ∨ hsame row supremumRead ∨
                hsame row handoffRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨ hsame row L ∨
              hsame row Q ∨ hsame row directedRead ∨ hsame row supremumRead ∨
                hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O I directedRead ∧ Cont S L supremumRead ∧
              Cont supremumRead Q handoffRead)
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
        intro row other sameRows source
        have lift : ∀ {target : BHist}, hsame row target -> hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl sameWindow =>
              exact Or.inl (lift sameWindow)
          | inr rest =>
              cases rest with
              | inl sameDirected =>
                  exact Or.inr (Or.inl (lift sameDirected))
              | inr restTail =>
                  cases restTail with
                  | inl sameSupremum =>
                      exact Or.inr (Or.inr (Or.inl (lift sameSupremum)))
                  | inr sameHandoff =>
                      exact Or.inr (Or.inr (Or.inr (lift sameHandoff)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameWindow =>
          exact Or.inr (Or.inr (Or.inl sameWindow))
      | inr rest =>
          cases rest with
          | inl sameDirected =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl sameDirected))))))
          | inr restTail =>
              cases restTail with
              | inl sameSupremum =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl sameSupremum)))))))
              | inr sameHandoff =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr sameHandoff)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, directedRoute, supremumRoute, handoffRoute⟩
  }
  exact ⟨cert, wUnary, directedUnary, supremumUnary, handoffUnary⟩

theorem DcpoCarrier_obligation_closure_package
    {O I W S M F Q L H C P N directedRead supremumRead completionRead replayRead :
      BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont O I directedRead →
        Cont S L supremumRead →
          Cont M F completionRead →
            Cont completionRead C replayRead →
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                      hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
                      Cont O I directedRead ∧ Cont S L supremumRead ∧
                        Cont M F completionRead ∧ Cont completionRead C replayRead)
                  hsame ∧
                UnaryHistory directedRead ∧ UnaryHistory supremumRead ∧
                  UnaryHistory completionRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute completionRoute replayRoute
  have carrierOriginal : DcpoCarrier O I W S M F Q L H C P N := carrier
  obtain ⟨oUnary, iUnary, _wUnary, sUnary, mUnary, fUnary, _qUnary, lUnary,
    _hUnary, cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed oUnary iUnary directedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary fUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary cUnary replayRoute
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
              Cont O I directedRead ∧ Cont S L supremumRead ∧
                Cont M F completionRead ∧ Cont completionRead C replayRead)
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
      exact
        ⟨source.right, carrierOriginal, directedRoute, supremumRoute, completionRoute,
          replayRoute⟩
  }
  exact ⟨cert, directedUnary, supremumUnary, completionUnary, replayUnary⟩

end BEDC.Derived.DcpoUp
