import BEDC.Derived.BoolUp

namespace BEDC.Derived.BoolUp

theorem BoolHistoryClassifier_endpoint_exactness {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k ↔
      (BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty ∧
          BEDC.FKernel.Hist.hsame k BEDC.FKernel.Hist.BHist.Empty) ∨
        (BEDC.FKernel.Hist.hsame h
            (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) ∧
          BEDC.FKernel.Hist.hsame k
            (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty)) := by
  constructor
  · exact BoolHistoryClassifier_cases
  · intro endpoints
    cases endpoints with
    | inl emptyEndpoints =>
        constructor
        · exact Or.inl emptyEndpoints.left
        · constructor
          · exact Or.inl emptyEndpoints.right
          · exact BEDC.FKernel.Hist.hsame_trans emptyEndpoints.left
              (BEDC.FKernel.Hist.hsame_symm emptyEndpoints.right)
    | inr oneEndpoints =>
        constructor
        · exact Or.inr oneEndpoints.left
        · constructor
          · exact Or.inr oneEndpoints.right
          · exact BEDC.FKernel.Hist.hsame_trans oneEndpoints.left
              (BEDC.FKernel.Hist.hsame_symm oneEndpoints.right)

theorem BoolHistoryClassifier_endpoint_bridge_exactness {v w : BEDC.FKernel.Mark.BMark} :
    BoolHistoryClassifier (BoolEndpoint v) (BoolEndpoint w) ↔
      BEDC.FKernel.Mark.msame v w := by
  constructor
  · intro classifier
    cases classifier with
    | intro _ rest =>
        cases rest with
        | intro _ endpointSame =>
            exact (BoolEndpoint_bridge_exactness (v := v) (w := w)).mpr endpointSame
  · intro sameVW
    have carrierV : BoolHistoryCarrier (BoolEndpoint v) := by
      cases v with
      | b0 =>
          exact Or.inl (BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty)
      | b1 =>
          exact Or.inr
            (BEDC.FKernel.Hist.hsame_refl
              (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty))
    have carrierW : BoolHistoryCarrier (BoolEndpoint w) := by
      cases w with
      | b0 =>
          exact Or.inl (BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty)
      | b1 =>
          exact Or.inr
            (BEDC.FKernel.Hist.hsame_refl
              (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty))
    exact ⟨carrierV, carrierW, (BoolEndpoint_bridge_exactness (v := v) (w := w)).mp sameVW⟩

theorem BoolHistoryClassifier_source_qualified_readback_exactness
    {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k ↔
      exists v : BEDC.FKernel.Mark.BMark, exists w : BEDC.FKernel.Mark.BMark,
        BoolSourceSpec v ∧ BoolSourceSpec w ∧
          BEDC.FKernel.Hist.hsame h (BoolEndpoint v) ∧
            BEDC.FKernel.Hist.hsame k (BoolEndpoint w) ∧
              BEDC.FKernel.Mark.msame v w := by
  constructor
  · intro classifier
    cases (BoolHistoryClassifier_mark_readback_exactness (h := h) (k := k)).mp
        classifier with
    | intro v rest =>
        cases rest with
        | intro w payload =>
            cases payload with
            | intro readH restPayload =>
                cases restPayload with
                | intro readK sameVW =>
                    have sourceV : BoolSourceSpec v := by
                      cases v with
                      | b0 =>
                          exact Or.inl
                            (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0)
                      | b1 =>
                          exact Or.inr
                            (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1)
                    have sourceW : BoolSourceSpec w := by
                      cases w with
                      | b0 =>
                          exact Or.inl
                            (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0)
                      | b1 =>
                          exact Or.inr
                            (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1)
                    exact Exists.intro v
                      (Exists.intro w
                        (And.intro sourceV
                          (And.intro sourceW
                            (And.intro readH (And.intro readK sameVW)))))
  · intro witness
    cases witness with
    | intro v rest =>
        cases rest with
        | intro w payload =>
            cases payload with
            | intro _sourceV restPayload =>
                cases restPayload with
                | intro _sourceW restPayload =>
                    cases restPayload with
                    | intro readH restPayload =>
                        cases restPayload with
                        | intro readK sameVW =>
                            exact
                              (BoolHistoryClassifier_mark_readback_exactness
                                (h := h) (k := k)).mpr
                                (Exists.intro v
                                  (Exists.intro w
                                    (And.intro readH (And.intro readK sameVW))))

theorem BoolEndpoint_classifier_exactness {v w : BEDC.FKernel.Mark.BMark} :
    BoolHistoryClassifier (BoolEndpoint v) (BoolEndpoint w) ↔
      BEDC.FKernel.Mark.msame v w := by
  constructor
  · intro classifier
    cases classifier with
    | intro _carrierV rest =>
        cases rest with
        | intro _carrierW sameEndpoints =>
            exact (BoolEndpoint_bridge_exactness (v := v) (w := w)).mpr sameEndpoints
  · intro sameVW
    have sameEndpoints :
        BEDC.FKernel.Hist.hsame (BoolEndpoint v) (BoolEndpoint w) :=
      (BoolEndpoint_bridge_exactness (v := v) (w := w)).mp sameVW
    have carrierV : BoolHistoryCarrier (BoolEndpoint v) :=
      (BoolHistoryCarrier_endpoint_coverage
        (h := BoolEndpoint v)).mpr
        (Exists.intro v
          (BEDC.FKernel.Hist.hsame_refl (BoolEndpoint v)))
    have carrierW : BoolHistoryCarrier (BoolEndpoint w) :=
      (BoolHistoryCarrier_endpoint_coverage
        (h := BoolEndpoint w)).mpr
        (Exists.intro w
          (BEDC.FKernel.Hist.hsame_refl (BoolEndpoint w)))
    exact And.intro carrierV (And.intro carrierW sameEndpoints)

end BEDC.Derived.BoolUp
