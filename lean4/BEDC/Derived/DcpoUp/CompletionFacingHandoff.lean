import BEDC.Derived.DcpoUp

namespace BEDC.Derived.DcpoUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DcpoCarrier_completion_facing_handoff
    {O I W S M F Q L H C P N directedRead supremumRead lowerRead completionRead
      replayRead : BHist} :
    DcpoCarrier O I W S M F Q L H C P N ->
      Cont O I directedRead ->
        Cont S L supremumRead ->
          Cont supremumRead L lowerRead ->
            Cont M F completionRead ->
              Cont completionRead Q replayRead ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row lowerRead ∨ hsame row completionRead ∨
                          hsame row replayRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                        hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row lowerRead ∨ hsame row completionRead ∨
                              hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
                        Cont O I directedRead ∧ Cont S L supremumRead ∧
                          Cont supremumRead L lowerRead ∧ Cont M F completionRead ∧
                            Cont completionRead Q replayRead)
                    hsame ∧
                  UnaryHistory lowerRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute lowerRoute completionRoute replayRoute
  have carrierWitness : DcpoCarrier O I W S M F Q L H C P N := carrier
  obtain ⟨_oUnary, _iUnary, _wUnary, sUnary, mUnary, fUnary, qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed supremumUnary lUnary lowerRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary fUnary completionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed completionUnary qUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lowerRead ∨ hsame row completionRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨ hsame row L ∨
              hsame row M ∨ hsame row F ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row lowerRead ∨
                  hsame row completionRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
              Cont O I directedRead ∧ Cont S L supremumRead ∧
                Cont supremumRead L lowerRead ∧ Cont M F completionRead ∧
                  Cont completionRead Q replayRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro lowerRead ⟨Or.inl (hsame_refl lowerRead), lowerUnary⟩
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
        have lift : forall {target : BHist}, hsame row target -> hsame other target := by
          intro _target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl sameLower =>
              exact Or.inl (lift sameLower)
          | inr rest =>
              cases rest with
              | inl sameCompletion =>
                  exact Or.inr (Or.inl (lift sameCompletion))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (lift sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLower =>
          repeat (first | exact Or.inl sameLower | apply Or.inr)
      | inr rest =>
          cases rest with
          | inl sameCompletion =>
              repeat (first | exact Or.inl sameCompletion | apply Or.inr)
          | inr sameReplay =>
              repeat (first | exact sameReplay | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierWitness, directedRoute, supremumRoute, lowerRoute,
          completionRoute, replayRoute⟩
  }
  exact ⟨cert, lowerUnary, completionUnary, replayUnary⟩

end BEDC.Derived.DcpoUp
