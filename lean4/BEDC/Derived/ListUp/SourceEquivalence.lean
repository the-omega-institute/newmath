import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_source_equivalence
    {relA relB : BEDC.FKernel.Hist.BHist → BEDC.FKernel.Hist.BHist → Prop}
    (rel_equiv : ∀ x y : BEDC.FKernel.Hist.BHist, relA x y ↔ relB x y) :
    ∀ {xs ys : BEDC.Derived.ListUp.ListCarrier BEDC.FKernel.Hist.BHist},
      BEDC.Derived.ListUp.ListClassifierSpec relA xs ys ↔
        BEDC.Derived.ListUp.ListClassifierSpec relB xs ys := by
  change ∀ {xs ys : BEDC.Derived.ListUp.ListCarrier BEDC.FKernel.Hist.BHist},
    BEDC.Derived.ListUp.ListClassifierSpec relA xs ys ↔
      BEDC.Derived.ListUp.ListClassifierSpec relB xs ys
  intro xs
  induction xs with
  | nil =>
      intro ys
      cases ys with
      | nil =>
          constructor
          · intro _
            constructor
          · intro _
            constructor
      | cons _ _ =>
          constructor
          · intro classified
            cases classified
          · intro classified
            cases classified
  | cons x xs ih =>
      intro ys
      cases ys with
      | nil =>
          constructor
          · intro classified
            cases classified
          · intro classified
            cases classified
      | cons y ys =>
          constructor
          · intro classified
            cases classified with
            | intro head tail =>
                constructor
                · exact (rel_equiv x y).mp head
                · exact (ih (ys := ys)).mp tail
          · intro classified
            cases classified with
            | intro head tail =>
                constructor
                · exact (rel_equiv x y).mpr head
                · exact (ih (ys := ys)).mpr tail

end BEDC.Derived.ListUp
