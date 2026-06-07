import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DnaBoundaryTriggerClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DnaBoundaryTriggerClosureUp : Type where
  | mk (B A T W F L H C P N : BHist) : DnaBoundaryTriggerClosureUp
  deriving DecidableEq

def dnaBoundaryTriggerClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dnaBoundaryTriggerClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dnaBoundaryTriggerClosureEncodeBHist h

def dnaBoundaryTriggerClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dnaBoundaryTriggerClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dnaBoundaryTriggerClosureDecodeBHist tail)

private theorem dnaBoundaryTriggerClosureDecode_encode_bhist :
    ∀ h : BHist, dnaBoundaryTriggerClosureDecodeBHist
      (dnaBoundaryTriggerClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dnaBoundaryTriggerClosureFields : DnaBoundaryTriggerClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DnaBoundaryTriggerClosureUp.mk B A T W F L H C P N => [B, A, T, W, F, L, H, C, P, N]

def dnaBoundaryTriggerClosureToEventFlow : DnaBoundaryTriggerClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dnaBoundaryTriggerClosureFields x).map dnaBoundaryTriggerClosureEncodeBHist

private def dnaBoundaryTriggerClosureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dnaBoundaryTriggerClosureEventAt index rest

def dnaBoundaryTriggerClosureFromEventFlow
    (ef : EventFlow) : Option DnaBoundaryTriggerClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DnaBoundaryTriggerClosureUp.mk
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 0 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 1 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 2 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 3 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 4 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 5 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 6 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 7 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 8 ef))
      (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEventAt 9 ef)))

private theorem dnaBoundaryTriggerClosure_round_trip :
    ∀ x : DnaBoundaryTriggerClosureUp,
      dnaBoundaryTriggerClosureFromEventFlow
        (dnaBoundaryTriggerClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A T W F L H C P N =>
      change
        some
          (DnaBoundaryTriggerClosureUp.mk
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist B))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist A))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist T))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist W))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist F))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist L))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist H))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist C))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist P))
            (dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist N))) =
          some (DnaBoundaryTriggerClosureUp.mk B A T W F L H C P N)
      rw [dnaBoundaryTriggerClosureDecode_encode_bhist B,
        dnaBoundaryTriggerClosureDecode_encode_bhist A,
        dnaBoundaryTriggerClosureDecode_encode_bhist T,
        dnaBoundaryTriggerClosureDecode_encode_bhist W,
        dnaBoundaryTriggerClosureDecode_encode_bhist F,
        dnaBoundaryTriggerClosureDecode_encode_bhist L,
        dnaBoundaryTriggerClosureDecode_encode_bhist H,
        dnaBoundaryTriggerClosureDecode_encode_bhist C,
        dnaBoundaryTriggerClosureDecode_encode_bhist P,
        dnaBoundaryTriggerClosureDecode_encode_bhist N]

private theorem dnaBoundaryTriggerClosureToEventFlow_injective {x y : DnaBoundaryTriggerClosureUp} :
    dnaBoundaryTriggerClosureToEventFlow x = dnaBoundaryTriggerClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dnaBoundaryTriggerClosureFromEventFlow (dnaBoundaryTriggerClosureToEventFlow x) =
        dnaBoundaryTriggerClosureFromEventFlow (dnaBoundaryTriggerClosureToEventFlow y) :=
    congrArg dnaBoundaryTriggerClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dnaBoundaryTriggerClosure_round_trip x).symm
      (Eq.trans hread (dnaBoundaryTriggerClosure_round_trip y)))

instance dnaBoundaryTriggerClosureBHistCarrier : BHistCarrier DnaBoundaryTriggerClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dnaBoundaryTriggerClosureToEventFlow
  fromEventFlow := dnaBoundaryTriggerClosureFromEventFlow

instance dnaBoundaryTriggerClosureChapterTasteGate :
    ChapterTasteGate DnaBoundaryTriggerClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dnaBoundaryTriggerClosureFromEventFlow
      (dnaBoundaryTriggerClosureToEventFlow x) = some x
    exact dnaBoundaryTriggerClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dnaBoundaryTriggerClosureToEventFlow_injective heq)

instance dnaBoundaryTriggerClosureFieldFaithful :
    FieldFaithful DnaBoundaryTriggerClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dnaBoundaryTriggerClosureFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk B₁ A₁ T₁ W₁ F₁ L₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk B₂ A₂ T₂ W₂ F₂ L₂ H₂ C₂ P₂ N₂ =>
            injection h with hB rest₁
            injection rest₁ with hA rest₂
            injection rest₂ with hT rest₃
            injection rest₃ with hW rest₄
            injection rest₄ with hF rest₅
            injection rest₅ with hL rest₆
            injection rest₆ with hH rest₇
            injection rest₇ with hC rest₈
            injection rest₈ with hP rest₉
            injection rest₉ with hN _
            cases hB
            cases hA
            cases hT
            cases hW
            cases hF
            cases hL
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance dnaBoundaryTriggerClosureNontrivial : Nontrivial DnaBoundaryTriggerClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DnaBoundaryTriggerClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DnaBoundaryTriggerClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty, by
        intro h
        injection h with hB _ _ _ _ _ _ _ _ _
        cases hB⟩

theorem DnaBoundaryTriggerClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dnaBoundaryTriggerClosureDecodeBHist (dnaBoundaryTriggerClosureEncodeBHist h) = h) ∧
      (∀ x : DnaBoundaryTriggerClosureUp,
        dnaBoundaryTriggerClosureFromEventFlow
          (dnaBoundaryTriggerClosureToEventFlow x) = some x) ∧
        (∀ x y : DnaBoundaryTriggerClosureUp,
          dnaBoundaryTriggerClosureToEventFlow x =
            dnaBoundaryTriggerClosureToEventFlow y -> x = y) ∧
          dnaBoundaryTriggerClosureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact dnaBoundaryTriggerClosureDecode_encode_bhist
  · constructor
    · exact dnaBoundaryTriggerClosure_round_trip
    · constructor
      · intro x y heq
        exact dnaBoundaryTriggerClosureToEventFlow_injective heq
      · rfl

end BEDC.Derived.DnaBoundaryTriggerClosureUp
