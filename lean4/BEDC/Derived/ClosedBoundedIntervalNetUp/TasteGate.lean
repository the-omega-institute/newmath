import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalNetUp : Type where
  | mk
      (located mesh rationalCells dyadicRefinements centers coverage streamWindows
        regSeqReadback realSeal transport route provenance name : BHist) :
      ClosedBoundedIntervalNetUp
  deriving DecidableEq

def closedBoundedIntervalNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalNetEncodeBHist h

def closedBoundedIntervalNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalNetDecodeBHist tail)

private theorem closedBoundedIntervalNet_decode_encode_bhist :
    ∀ h : BHist,
      closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedBoundedIntervalNetFields : ClosedBoundedIntervalNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
      coverage streamWindows regSeqReadback realSeal transport route provenance name =>
      [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
        regSeqReadback, realSeal, transport, route, provenance, name]

def closedBoundedIntervalNetToEventFlow : ClosedBoundedIntervalNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedBoundedIntervalNetFields x).map closedBoundedIntervalNetEncodeBHist

private def closedBoundedIntervalNetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedBoundedIntervalNetEventAtDefault index rest

def closedBoundedIntervalNetFromEventFlow
    (ef : EventFlow) : Option ClosedBoundedIntervalNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedBoundedIntervalNetUp.mk
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 0 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 1 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 2 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 3 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 4 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 5 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 6 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 7 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 8 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 9 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 10 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 11 ef))
      (closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEventAtDefault 12 ef)))

private theorem closedBoundedIntervalNet_round_trip :
    ∀ x : ClosedBoundedIntervalNetUp,
      closedBoundedIntervalNetFromEventFlow (closedBoundedIntervalNetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk located mesh rationalCells dyadicRefinements centers coverage streamWindows
      regSeqReadback realSeal transport route provenance name =>
      change
        some
          (ClosedBoundedIntervalNetUp.mk
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist located))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist mesh))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist rationalCells))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist dyadicRefinements))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist centers))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist coverage))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist streamWindows))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist regSeqReadback))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist realSeal))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist transport))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist route))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist provenance))
            (closedBoundedIntervalNetDecodeBHist
              (closedBoundedIntervalNetEncodeBHist name))) =
          some
            (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
              coverage streamWindows regSeqReadback realSeal transport route provenance name)
      rw [closedBoundedIntervalNet_decode_encode_bhist located,
        closedBoundedIntervalNet_decode_encode_bhist mesh,
        closedBoundedIntervalNet_decode_encode_bhist rationalCells,
        closedBoundedIntervalNet_decode_encode_bhist dyadicRefinements,
        closedBoundedIntervalNet_decode_encode_bhist centers,
        closedBoundedIntervalNet_decode_encode_bhist coverage,
        closedBoundedIntervalNet_decode_encode_bhist streamWindows,
        closedBoundedIntervalNet_decode_encode_bhist regSeqReadback,
        closedBoundedIntervalNet_decode_encode_bhist realSeal,
        closedBoundedIntervalNet_decode_encode_bhist transport,
        closedBoundedIntervalNet_decode_encode_bhist route,
        closedBoundedIntervalNet_decode_encode_bhist provenance,
        closedBoundedIntervalNet_decode_encode_bhist name]

private theorem closedBoundedIntervalNetToEventFlow_injective
    {x y : ClosedBoundedIntervalNetUp} :
    closedBoundedIntervalNetToEventFlow x = closedBoundedIntervalNetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalNetFromEventFlow (closedBoundedIntervalNetToEventFlow x) =
        closedBoundedIntervalNetFromEventFlow (closedBoundedIntervalNetToEventFlow y) :=
    congrArg closedBoundedIntervalNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedBoundedIntervalNet_round_trip x).symm
      (Eq.trans hread (closedBoundedIntervalNet_round_trip y)))

private theorem closedBoundedIntervalNet_fields_faithful :
    ∀ x y : ClosedBoundedIntervalNetUp,
      closedBoundedIntervalNetFields x = closedBoundedIntervalNetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk l₁ m₁ q₁ d₁ z₁ f₁ s₁ r₁ e₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk l₂ m₂ q₂ d₂ z₂ f₂ s₂ r₂ e₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance closedBoundedIntervalNetBHistCarrier :
    BHistCarrier ClosedBoundedIntervalNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalNetToEventFlow
  fromEventFlow := closedBoundedIntervalNetFromEventFlow

instance closedBoundedIntervalNetChapterTasteGate :
    ChapterTasteGate ClosedBoundedIntervalNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedBoundedIntervalNetFromEventFlow (closedBoundedIntervalNetToEventFlow x) =
      some x
    exact closedBoundedIntervalNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedBoundedIntervalNetToEventFlow_injective heq)

instance closedBoundedIntervalNetFieldFaithful :
    FieldFaithful ClosedBoundedIntervalNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedBoundedIntervalNetFields
  field_faithful := closedBoundedIntervalNet_fields_faithful

instance closedBoundedIntervalNetNontrivial : Nontrivial ClosedBoundedIntervalNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedBoundedIntervalNetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ClosedBoundedIntervalNetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ClosedBoundedIntervalNetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedBoundedIntervalNetUp) ∧
      Nonempty (FieldFaithful ClosedBoundedIntervalNetUp) ∧
        Nonempty (Nontrivial ClosedBoundedIntervalNetUp) ∧
          (∀ h : BHist,
            closedBoundedIntervalNetDecodeBHist (closedBoundedIntervalNetEncodeBHist h) =
              h) ∧
            (∀ x : ClosedBoundedIntervalNetUp,
              closedBoundedIntervalNetFromEventFlow (closedBoundedIntervalNetToEventFlow x) =
                some x) ∧
              closedBoundedIntervalNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨closedBoundedIntervalNetChapterTasteGate⟩,
      ⟨⟨closedBoundedIntervalNetFieldFaithful⟩,
        ⟨⟨closedBoundedIntervalNetNontrivial⟩,
          closedBoundedIntervalNet_decode_encode_bhist,
          closedBoundedIntervalNet_round_trip,
          rfl⟩⟩⟩

theorem ClosedBoundedIntervalNetCoverageRoute_semantic_name_certificate :
    SemanticNameCert
      (fun row : BHist =>
        exists located mesh rationalCells dyadicRefinements centers coverage streamWindows
            regSeqReadback realSeal transport route provenance name : BHist,
          row = coverage /\
            closedBoundedIntervalNetFields
                (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements
                  centers coverage streamWindows regSeqReadback realSeal transport route provenance
                  name) =
              [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
                regSeqReadback, realSeal, transport, route, provenance, name])
      (fun row : BHist =>
        exists located mesh rationalCells dyadicRefinements centers coverage streamWindows
            regSeqReadback realSeal transport route provenance name : BHist,
          row = coverage /\
            closedBoundedIntervalNetFields
                (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements
                  centers coverage streamWindows regSeqReadback realSeal transport route provenance
                  name) =
              [located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
                regSeqReadback, realSeal, transport, route, provenance, name])
      (fun row : BHist =>
        exists x : ClosedBoundedIntervalNetUp,
          row = BHist.Empty \/ closedBoundedIntervalNetFields x = closedBoundedIntervalNetFields x)
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
          regSeqReadback, realSeal, transport, route, provenance, name, _rowCoverage,
          _fields⟩
      exact
        Exists.intro
          (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
            coverage streamWindows regSeqReadback realSeal transport route provenance name)
          (Or.inr rfl)
  }

theorem ClosedBoundedIntervalNetRealSeal_nonescape :
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
        ∃ x : ClosedBoundedIntervalNetUp,
          row = BHist.Empty ∨ closedBoundedIntervalNetFields x = closedBoundedIntervalNetFields x)
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
      rcases source with
        ⟨located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
          regSeqReadback, realSeal, transport, route, provenance, name, _rowSeal,
          _fields⟩
      exact
        Exists.intro
          (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
            coverage streamWindows regSeqReadback realSeal transport route provenance name)
          (Or.inr rfl)
    ledger_sound := by
      intro _row source
      rcases source with
        ⟨located, mesh, rationalCells, dyadicRefinements, centers, coverage, streamWindows,
          regSeqReadback, realSeal, transport, route, provenance, name, _rowSeal,
          _fields⟩
      exact
        Exists.intro
          (ClosedBoundedIntervalNetUp.mk located mesh rationalCells dyadicRefinements centers
            coverage streamWindows regSeqReadback realSeal transport route provenance name)
          (Or.inr rfl)
  }

end BEDC.Derived.ClosedBoundedIntervalNetUp
