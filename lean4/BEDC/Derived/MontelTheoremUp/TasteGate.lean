import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MontelTheoremUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MontelTheoremUp : Type where
  | mk
      (compactWindow localBounded equicontinuity uniformCauchy uniformLimit
        holomorphicReadback regularReadback dyadicTolerance terminalSeal transport replay
        provenance name : BHist) : MontelTheoremUp
  deriving DecidableEq

def montelTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: montelTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: montelTheoremEncodeBHist h

def montelTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (montelTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (montelTheoremDecodeBHist tail)

private theorem montelTheoremDecode_encode_bhist :
    ∀ h : BHist, montelTheoremDecodeBHist (montelTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def montelTheoremToEventFlow : MontelTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MontelTheoremUp.mk compactWindow localBounded equicontinuity uniformCauchy
      uniformLimit holomorphicReadback regularReadback dyadicTolerance terminalSeal transport
      replay provenance name =>
      [[BMark.b0],
        montelTheoremEncodeBHist compactWindow,
        [BMark.b1, BMark.b0],
        montelTheoremEncodeBHist localBounded,
        [BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist equicontinuity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist uniformCauchy,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist uniformLimit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist holomorphicReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        montelTheoremEncodeBHist dyadicTolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        montelTheoremEncodeBHist terminalSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        montelTheoremEncodeBHist name]

private def montelTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => montelTheoremEventAtDefault index rest

def montelTheoremFromEventFlow (ef : EventFlow) : Option MontelTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MontelTheoremUp.mk
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 1 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 3 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 5 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 7 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 9 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 11 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 13 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 15 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 17 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 19 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 21 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 23 ef))
      (montelTheoremDecodeBHist (montelTheoremEventAtDefault 25 ef)))

def montelTheoremFields : MontelTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MontelTheoremUp.mk compactWindow localBounded equicontinuity uniformCauchy
      uniformLimit holomorphicReadback regularReadback dyadicTolerance terminalSeal transport
      replay provenance name =>
      [compactWindow, localBounded, equicontinuity, uniformCauchy, uniformLimit,
        holomorphicReadback, regularReadback, dyadicTolerance, terminalSeal, transport,
        replay, provenance, name]

private theorem montelTheorem_round_trip :
    ∀ x : MontelTheoremUp,
      montelTheoremFromEventFlow (montelTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactWindow localBounded equicontinuity uniformCauchy uniformLimit
      holomorphicReadback regularReadback dyadicTolerance terminalSeal transport replay
      provenance name =>
      change
        some
          (MontelTheoremUp.mk
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist compactWindow))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist localBounded))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist equicontinuity))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist uniformCauchy))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist uniformLimit))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist holomorphicReadback))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist regularReadback))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist dyadicTolerance))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist terminalSeal))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist transport))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist replay))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist provenance))
            (montelTheoremDecodeBHist (montelTheoremEncodeBHist name))) =
          some
            (MontelTheoremUp.mk compactWindow localBounded equicontinuity uniformCauchy
              uniformLimit holomorphicReadback regularReadback dyadicTolerance terminalSeal
              transport replay provenance name)
      rw [montelTheoremDecode_encode_bhist compactWindow,
        montelTheoremDecode_encode_bhist localBounded,
        montelTheoremDecode_encode_bhist equicontinuity,
        montelTheoremDecode_encode_bhist uniformCauchy,
        montelTheoremDecode_encode_bhist uniformLimit,
        montelTheoremDecode_encode_bhist holomorphicReadback,
        montelTheoremDecode_encode_bhist regularReadback,
        montelTheoremDecode_encode_bhist dyadicTolerance,
        montelTheoremDecode_encode_bhist terminalSeal,
        montelTheoremDecode_encode_bhist transport,
        montelTheoremDecode_encode_bhist replay,
        montelTheoremDecode_encode_bhist provenance,
        montelTheoremDecode_encode_bhist name]

private theorem montelTheoremToEventFlow_injective {x y : MontelTheoremUp} :
    montelTheoremToEventFlow x = montelTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      montelTheoremFromEventFlow (montelTheoremToEventFlow x) =
        montelTheoremFromEventFlow (montelTheoremToEventFlow y) :=
    congrArg montelTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (montelTheorem_round_trip x).symm
      (Eq.trans hread (montelTheorem_round_trip y)))

private theorem montelTheoremFields_faithful :
    ∀ x y : MontelTheoremUp, montelTheoremFields x = montelTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk compactWindow₁ localBounded₁ equicontinuity₁ uniformCauchy₁ uniformLimit₁
      holomorphicReadback₁ regularReadback₁ dyadicTolerance₁ terminalSeal₁ transport₁
      replay₁ provenance₁ name₁ =>
      cases y with
      | mk compactWindow₂ localBounded₂ equicontinuity₂ uniformCauchy₂ uniformLimit₂
          holomorphicReadback₂ regularReadback₂ dyadicTolerance₂ terminalSeal₂ transport₂
          replay₂ provenance₂ name₂ =>
          injection h with hCompact rest₁
          injection rest₁ with hLocal rest₂
          injection rest₂ with hEqui rest₃
          injection rest₃ with hCauchy rest₄
          injection rest₄ with hLimit rest₅
          injection rest₅ with hHolomorphic rest₆
          injection rest₆ with hRegular rest₇
          injection rest₇ with hDyadic rest₈
          injection rest₈ with hSeal rest₉
          injection rest₉ with hTransport rest₁₀
          injection rest₁₀ with hReplay rest₁₁
          injection rest₁₁ with hProvenance rest₁₂
          injection rest₁₂ with hName _
          cases hCompact
          cases hLocal
          cases hEqui
          cases hCauchy
          cases hLimit
          cases hHolomorphic
          cases hRegular
          cases hDyadic
          cases hSeal
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hName
          rfl

instance montelTheoremBHistCarrier : BHistCarrier MontelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := montelTheoremToEventFlow
  fromEventFlow := montelTheoremFromEventFlow

instance montelTheoremChapterTasteGate : ChapterTasteGate MontelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change montelTheoremFromEventFlow (montelTheoremToEventFlow x) = some x
    exact montelTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (montelTheoremToEventFlow_injective heq)

instance montelTheoremFieldFaithful : FieldFaithful MontelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := montelTheoremFields
  field_faithful := montelTheoremFields_faithful

instance montelTheoremNontrivial : Nontrivial MontelTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MontelTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      MontelTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty, by
        intro h
        injection h with hCompact _ _ _ _ _ _ _ _ _ _ _ _
        cases hCompact⟩

theorem MontelTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, montelTheoremDecodeBHist (montelTheoremEncodeBHist h) = h) ∧
      (∀ x : MontelTheoremUp,
        montelTheoremFromEventFlow (montelTheoremToEventFlow x) = some x) ∧
        (∀ x y : MontelTheoremUp,
          montelTheoremToEventFlow x = montelTheoremToEventFlow y → x = y) ∧
          montelTheoremEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : MontelTheoremUp, montelTheoremFields x = montelTheoremFields y →
              x = y) ∧
              (∃ x y : MontelTheoremUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact montelTheoremDecode_encode_bhist
  · constructor
    · exact montelTheorem_round_trip
    · constructor
      · intro x y heq
        exact montelTheoremToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact montelTheoremFields_faithful
          · exact
              ⟨MontelTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                MontelTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
                  intro h
                  injection h with hCompact _ _ _ _ _ _ _ _ _ _ _ _
                  cases hCompact⟩

end BEDC.Derived.MontelTheoremUp.TasteGate
