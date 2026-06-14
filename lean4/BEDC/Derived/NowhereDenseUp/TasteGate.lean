import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NowhereDenseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NowhereDenseUp : Type where
  | mk (T B F E D M H C P N : BHist) : NowhereDenseUp
  deriving DecidableEq

def nowhereDenseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nowhereDenseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nowhereDenseEncodeBHist h

def nowhereDenseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nowhereDenseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nowhereDenseDecodeBHist tail)

private theorem NowhereDenseTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, nowhereDenseDecodeBHist (nowhereDenseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nowhereDenseFields : NowhereDenseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NowhereDenseUp.mk T B F E D M H C P N => [T, B, F, E, D, M, H, C, P, N]

def nowhereDenseToEventFlow : NowhereDenseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (nowhereDenseFields x).map nowhereDenseEncodeBHist

def nowhereDenseFromEventFlow : EventFlow → Option NowhereDenseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | T :: B :: F :: E :: D :: M :: H :: C :: P :: N :: [] =>
        some
          (NowhereDenseUp.mk
            (nowhereDenseDecodeBHist T)
            (nowhereDenseDecodeBHist B)
            (nowhereDenseDecodeBHist F)
            (nowhereDenseDecodeBHist E)
            (nowhereDenseDecodeBHist D)
            (nowhereDenseDecodeBHist M)
            (nowhereDenseDecodeBHist H)
            (nowhereDenseDecodeBHist C)
            (nowhereDenseDecodeBHist P)
            (nowhereDenseDecodeBHist N))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

private theorem NowhereDenseTasteGate_single_carrier_alignment_round_trip
    (x : NowhereDenseUp) :
    nowhereDenseFromEventFlow (nowhereDenseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T B F E D M H C P N =>
      change
        some
          (NowhereDenseUp.mk
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist T))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist B))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist F))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist E))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist D))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist M))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist H))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist C))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist P))
            (nowhereDenseDecodeBHist (nowhereDenseEncodeBHist N))) =
          some (NowhereDenseUp.mk T B F E D M H C P N)
      rw [NowhereDenseTasteGate_single_carrier_alignment_decode T,
        NowhereDenseTasteGate_single_carrier_alignment_decode B,
        NowhereDenseTasteGate_single_carrier_alignment_decode F,
        NowhereDenseTasteGate_single_carrier_alignment_decode E,
        NowhereDenseTasteGate_single_carrier_alignment_decode D,
        NowhereDenseTasteGate_single_carrier_alignment_decode M,
        NowhereDenseTasteGate_single_carrier_alignment_decode H,
        NowhereDenseTasteGate_single_carrier_alignment_decode C,
        NowhereDenseTasteGate_single_carrier_alignment_decode P,
        NowhereDenseTasteGate_single_carrier_alignment_decode N]

private theorem NowhereDenseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NowhereDenseUp} :
    nowhereDenseToEventFlow x = nowhereDenseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nowhereDenseFromEventFlow (nowhereDenseToEventFlow x) =
        nowhereDenseFromEventFlow (nowhereDenseToEventFlow y) :=
    congrArg nowhereDenseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NowhereDenseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NowhereDenseTasteGate_single_carrier_alignment_round_trip y)))

private theorem NowhereDenseTasteGate_single_carrier_alignment_fields_faithful
    (x y : NowhereDenseUp) :
    nowhereDenseFields x = nowhereDenseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk T₁ B₁ F₁ E₁ D₁ M₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ B₂ F₂ E₂ D₂ M₂ H₂ C₂ P₂ N₂ =>
          injection h with hT hRest₁
          injection hRest₁ with hB hRest₂
          injection hRest₂ with hF hRest₃
          injection hRest₃ with hE hRest₄
          injection hRest₄ with hD hRest₅
          injection hRest₅ with hM hRest₆
          injection hRest₆ with hH hRest₇
          injection hRest₇ with hC hRest₈
          injection hRest₈ with hP hRest₉
          injection hRest₉ with hN _
          subst hT
          subst hB
          subst hF
          subst hE
          subst hD
          subst hM
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance nowhereDenseBHistCarrier : BHistCarrier NowhereDenseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nowhereDenseToEventFlow
  fromEventFlow := nowhereDenseFromEventFlow

instance nowhereDenseChapterTasteGate : ChapterTasteGate NowhereDenseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nowhereDenseFromEventFlow (nowhereDenseToEventFlow x) = some x
    exact NowhereDenseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NowhereDenseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance nowhereDenseFieldFaithful : FieldFaithful NowhereDenseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nowhereDenseFields
  field_faithful := NowhereDenseTasteGate_single_carrier_alignment_fields_faithful

instance nowhereDenseNontrivial : Nontrivial NowhereDenseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NowhereDenseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NowhereDenseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NowhereDenseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nowhereDenseChapterTasteGate

theorem NowhereDenseTasteGate_single_carrier_alignment :
    (∀ h : BHist, nowhereDenseDecodeBHist (nowhereDenseEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NowhereDenseUp) ∧
        Nonempty (ChapterTasteGate NowhereDenseUp) ∧
          nowhereDenseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨NowhereDenseTasteGate_single_carrier_alignment_decode,
      Nonempty.intro
        { toEventFlow := nowhereDenseToEventFlow
          fromEventFlow := nowhereDenseFromEventFlow },
      Nonempty.intro
        { round_trip := by
            intro x
            change nowhereDenseFromEventFlow (nowhereDenseToEventFlow x) = some x
            exact NowhereDenseTasteGate_single_carrier_alignment_round_trip x
          layer_separation := by
            intro x y hxy heq
            exact hxy (NowhereDenseTasteGate_single_carrier_alignment_toEventFlow_injective heq) },
      rfl⟩

end BEDC.Derived.NowhereDenseUp
