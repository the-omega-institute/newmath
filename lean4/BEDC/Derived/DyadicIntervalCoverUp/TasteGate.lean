import BEDC.Derived.DyadicIntervalCoverUp

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem DyadicIntervalCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist h) = h) ∧
      (∀ x : DyadicIntervalCoverUp,
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x) ∧
        (∀ x y : DyadicIntervalCoverUp,
          dyadicIntervalCoverToEventFlow x = dyadicIntervalCoverToEventFlow y → x = y) ∧
          dyadicIntervalCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist, dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hround :
      ∀ x : DyadicIntervalCoverUp,
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x := by
    intro x
    cases x with
    | mk L U M R V W Q A H C P N =>
        change
          some
            (DyadicIntervalCoverUp.mk
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist L))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist U))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist M))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist R))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist V))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist W))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist Q))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist A))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist H))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist C))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist P))
              (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist N))) =
            some (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N)
        rw [hdecode L, hdecode U, hdecode M, hdecode R, hdecode V, hdecode W,
          hdecode Q, hdecode A, hdecode H, hdecode C, hdecode P, hdecode N]
  have hinj :
      ∀ x y : DyadicIntervalCoverUp,
        dyadicIntervalCoverToEventFlow x = dyadicIntervalCoverToEventFlow y → x = y := by
    intro x y heq
    have hread :
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) =
          dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow y) :=
      congrArg dyadicIntervalCoverFromEventFlow heq
    exact Option.some.inj (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact ⟨hdecode, hround, hinj, rfl⟩

theorem DyadicIntervalCoverEndpointRowAdmission
    (x : DyadicIntervalCoverUp) :
    (∃ L U M R V W Q A H C P N : BHist,
      x = DyadicIntervalCoverUp.mk L U M R V W Q A H C P N ∧
      dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x) ∧
      dyadicIntervalCoverEncodeBHist BHist.Empty = ([] : RawEvent) ∧
        dyadicIntervalCoverEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      exact
        ⟨⟨L, U, M, R, V, W, Q, A, H, C, P, N, rfl,
            (DyadicIntervalCoverTasteGate_single_carrier_alignment).right.left
              (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N)⟩,
          rfl, rfl⟩

end BEDC.Derived.DyadicIntervalCoverUp
