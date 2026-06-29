import BEDC.Derived.DcpoUp

namespace BEDC.Derived.DcpoUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DcpoCarrier_directed_supremum_scope
    {O I W S M F Q L H C P N directedRead supremumRead lowerRead handoffRead :
      BHist} :
    DcpoCarrier O I W S M F Q L H C P N →
      Cont O I directedRead →
        Cont S L supremumRead →
          Cont supremumRead L lowerRead →
            Cont M F handoffRead →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row directedRead ∨ hsame row supremumRead ∨
                        hsame row lowerRead ∨ hsame row handoffRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨
                      hsame row L ∨ hsame row M ∨ hsame row F ∨ hsame row Q ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row directedRead ∨ hsame row supremumRead ∨
                            hsame row lowerRead ∨ hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
                      Cont O I directedRead ∧ Cont S L supremumRead ∧
                        Cont supremumRead L lowerRead ∧ Cont M F handoffRead)
                  hsame ∧
                UnaryHistory directedRead ∧ UnaryHistory supremumRead ∧
                  UnaryHistory lowerRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro carrier directedRoute supremumRoute lowerRoute handoffRoute
  have carrierOriginal : DcpoCarrier O I W S M F Q L H C P N := carrier
  obtain ⟨oUnary, iUnary, _wUnary, sUnary, mUnary, fUnary, _qUnary, lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _orderWindow, _filterCompletion⟩ := carrier
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed oUnary iUnary directedRoute
  have supremumUnary : UnaryHistory supremumRead :=
    unary_cont_closed sUnary lUnary supremumRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed supremumUnary lUnary lowerRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed mUnary fUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row directedRead ∨ hsame row supremumRead ∨ hsame row lowerRead ∨
                hsame row handoffRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row O ∨ hsame row I ∨ hsame row W ∨ hsame row S ∨ hsame row L ∨
              hsame row M ∨ hsame row F ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row directedRead ∨
                  hsame row supremumRead ∨ hsame row lowerRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ DcpoCarrier O I W S M F Q L H C P N ∧
              Cont O I directedRead ∧ Cont S L supremumRead ∧
                Cont supremumRead L lowerRead ∧ Cont M F handoffRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro directedRead ⟨Or.inl (hsame_refl directedRead), directedUnary⟩
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
        constructor
        · cases source.left with
          | inl sameDirected =>
              exact Or.inl (lift sameDirected)
          | inr rest =>
              cases rest with
              | inl sameSupremum =>
                  exact Or.inr (Or.inl (lift sameSupremum))
              | inr restTail =>
                  cases restTail with
                  | inl sameLower =>
                      exact Or.inr (Or.inr (Or.inl (lift sameLower)))
                  | inr sameHandoff =>
                      exact Or.inr (Or.inr (Or.inr (lift sameHandoff)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      have patternFromTail :
          (hsame _row directedRead ∨ hsame _row supremumRead ∨
              hsame _row lowerRead ∨ hsame _row handoffRead) →
          hsame _row O ∨ hsame _row I ∨ hsame _row W ∨ hsame _row S ∨
            hsame _row L ∨ hsame _row M ∨ hsame _row F ∨ hsame _row Q ∨
              hsame _row H ∨ hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
                hsame _row directedRead ∨ hsame _row supremumRead ∨
                  hsame _row lowerRead ∨ hsame _row handoffRead := by
        intro tail
        have p12 :
            hsame _row N ∨ hsame _row directedRead ∨ hsame _row supremumRead ∨
              hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr tail
        have p11 :
            hsame _row P ∨ hsame _row N ∨ hsame _row directedRead ∨
              hsame _row supremumRead ∨ hsame _row lowerRead ∨
                hsame _row handoffRead :=
          Or.inr p12
        have p10 :
            hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
              hsame _row directedRead ∨ hsame _row supremumRead ∨
                hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr p11
        have p9 :
            hsame _row H ∨ hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
              hsame _row directedRead ∨ hsame _row supremumRead ∨
                hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr p10
        have p8 :
            hsame _row Q ∨ hsame _row H ∨ hsame _row C ∨ hsame _row P ∨
              hsame _row N ∨ hsame _row directedRead ∨ hsame _row supremumRead ∨
                hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr p9
        have p7 :
            hsame _row F ∨ hsame _row Q ∨ hsame _row H ∨ hsame _row C ∨
              hsame _row P ∨ hsame _row N ∨ hsame _row directedRead ∨
                hsame _row supremumRead ∨ hsame _row lowerRead ∨
                  hsame _row handoffRead :=
          Or.inr p8
        have p6 :
            hsame _row M ∨ hsame _row F ∨ hsame _row Q ∨ hsame _row H ∨
              hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
                hsame _row directedRead ∨ hsame _row supremumRead ∨
                  hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr p7
        have p5 :
            hsame _row L ∨ hsame _row M ∨ hsame _row F ∨ hsame _row Q ∨
              hsame _row H ∨ hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
                hsame _row directedRead ∨ hsame _row supremumRead ∨
                  hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr p6
        have p4 :
            hsame _row S ∨ hsame _row L ∨ hsame _row M ∨ hsame _row F ∨
              hsame _row Q ∨ hsame _row H ∨ hsame _row C ∨ hsame _row P ∨
                hsame _row N ∨ hsame _row directedRead ∨
                  hsame _row supremumRead ∨ hsame _row lowerRead ∨
                    hsame _row handoffRead :=
          Or.inr p5
        have p3 :
            hsame _row W ∨ hsame _row S ∨ hsame _row L ∨ hsame _row M ∨
              hsame _row F ∨ hsame _row Q ∨ hsame _row H ∨ hsame _row C ∨
                hsame _row P ∨ hsame _row N ∨ hsame _row directedRead ∨
                  hsame _row supremumRead ∨ hsame _row lowerRead ∨
                    hsame _row handoffRead :=
          Or.inr p4
        have p2 :
            hsame _row I ∨ hsame _row W ∨ hsame _row S ∨ hsame _row L ∨
              hsame _row M ∨ hsame _row F ∨ hsame _row Q ∨ hsame _row H ∨
                hsame _row C ∨ hsame _row P ∨ hsame _row N ∨
                  hsame _row directedRead ∨ hsame _row supremumRead ∨
                    hsame _row lowerRead ∨ hsame _row handoffRead :=
          Or.inr p3
        exact Or.inr p2
      exact patternFromTail source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierOriginal, directedRoute, supremumRoute, lowerRoute,
          handoffRoute⟩
  }
  exact ⟨cert, directedUnary, supremumUnary, lowerUnary, handoffUnary⟩

end BEDC.Derived.DcpoUp
