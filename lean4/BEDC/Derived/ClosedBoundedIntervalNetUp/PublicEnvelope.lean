import BEDC.Derived.ClosedBoundedIntervalNetUp.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ClosedBoundedIntervalNetPublicEnvelope :
    SemanticNameCert
      (fun row : BHist =>
        ∃ located mesh rationalCells dyadicRefinements centers coverage streamWindows
            regSeqReadback realSeal transport route provenance name : BHist,
          row = realSeal ∧
            closedBoundedIntervalNetFields
                (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements
                  centers coverage streamWindows regSeqReadback realSeal transport route provenance
                  name) =
              [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
                regSeqReadback, realSeal, transport, route, provenance, name])
      (fun row : BHist =>
        ∃ located mesh rationalCells dyadicRefinements centers coverage streamWindows
            regSeqReadback realSeal transport route provenance name : BHist,
          row = realSeal ∧
            closedBoundedIntervalNetFields
                (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements
                  centers coverage streamWindows regSeqReadback realSeal transport route provenance
                  name) =
              [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
                regSeqReadback, realSeal, transport, route, provenance, name])
      (fun row : BHist =>
        ∃ x : ClosedBoundedIntervalNetUp,
          row = BHist.Empty ∨ closedBoundedIntervalNetFields x = closedBoundedIntervalNetFields x)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := by
        exact
          Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (Exists.intro BHist.Empty
                (Exists.intro BHist.Empty
                  (Exists.intro BHist.Empty
                    (Exists.intro BHist.Empty
                      (Exists.intro BHist.Empty
                        (Exists.intro BHist.Empty
                          (Exists.intro BHist.Empty
                            (Exists.intro BHist.Empty
                              (Exists.intro BHist.Empty
                                (Exists.intro BHist.Empty
                                  (Exists.intro BHist.Empty
                                    (Exists.intro BHist.Empty
                                      (And.intro rfl rfl))))))))))))))
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
      exact source
    ledger_sound := by
      intro _row source
      rcases source with
        ⟨located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
          regSeqReadback, realSeal, transport, route, provenance, name, _rowSeal, _fields⟩
      exact
        Exists.intro
          (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
            coverage streamWindows regSeqReadback realSeal transport route provenance name)
          (Or.inr rfl)
  }

end BEDC.Derived.ClosedBoundedIntervalNetUp
