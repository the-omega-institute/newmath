import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitCauchyCriterionUp : Type where
  | mk (F W M S R E H C P N : BHist) : UniformLimitCauchyCriterionUp
  deriving DecidableEq

def uniformLimitCauchyCriterionFields :
    UniformLimitCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitCauchyCriterionUp.mk F W M S R E H C P N => [F, W, M, S, R, E, H, C, P, N]

def uniformLimitCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitCauchyCriterionEncodeBHist h

def uniformLimitCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitCauchyCriterionDecodeBHist tail)

private theorem uniformLimitCauchyCriterion_decode_encode :
    ∀ h : BHist,
      uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLimitCauchyCriterionToEventFlow :
    UniformLimitCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map uniformLimitCauchyCriterionEncodeBHist
      (uniformLimitCauchyCriterionFields x)

private def uniformLimitCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformLimitCauchyCriterionEventAtDefault index rest

def uniformLimitCauchyCriterionFromEventFlow
    (ef : EventFlow) : Option UniformLimitCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformLimitCauchyCriterionUp.mk
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 0 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 1 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 2 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 3 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 4 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 5 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 6 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 7 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 8 ef))
      (uniformLimitCauchyCriterionDecodeBHist
        (uniformLimitCauchyCriterionEventAtDefault 9 ef)))

private theorem uniformLimitCauchyCriterion_round_trip :
    ∀ x : UniformLimitCauchyCriterionUp,
      uniformLimitCauchyCriterionFromEventFlow
        (uniformLimitCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W M S R E H C P N =>
      change
        some
          (UniformLimitCauchyCriterionUp.mk
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist F))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist W))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist M))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist S))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist R))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist E))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist H))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist C))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist P))
            (uniformLimitCauchyCriterionDecodeBHist
              (uniformLimitCauchyCriterionEncodeBHist N))) =
          some (UniformLimitCauchyCriterionUp.mk F W M S R E H C P N)
      rw [uniformLimitCauchyCriterion_decode_encode F,
        uniformLimitCauchyCriterion_decode_encode W,
        uniformLimitCauchyCriterion_decode_encode M,
        uniformLimitCauchyCriterion_decode_encode S,
        uniformLimitCauchyCriterion_decode_encode R,
        uniformLimitCauchyCriterion_decode_encode E,
        uniformLimitCauchyCriterion_decode_encode H,
        uniformLimitCauchyCriterion_decode_encode C,
        uniformLimitCauchyCriterion_decode_encode P,
        uniformLimitCauchyCriterion_decode_encode N]

private theorem uniformLimitCauchyCriterionToEventFlow_injective
    {x y : UniformLimitCauchyCriterionUp} :
    uniformLimitCauchyCriterionToEventFlow x =
      uniformLimitCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitCauchyCriterionFromEventFlow
          (uniformLimitCauchyCriterionToEventFlow x) =
        uniformLimitCauchyCriterionFromEventFlow
          (uniformLimitCauchyCriterionToEventFlow y) :=
    congrArg uniformLimitCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLimitCauchyCriterion_round_trip x).symm
      (Eq.trans hread (uniformLimitCauchyCriterion_round_trip y)))

instance uniformLimitCauchyCriterionBHistCarrier :
    BHistCarrier UniformLimitCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitCauchyCriterionToEventFlow
  fromEventFlow := uniformLimitCauchyCriterionFromEventFlow

instance uniformLimitCauchyCriterionChapterTasteGate :
    ChapterTasteGate UniformLimitCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformLimitCauchyCriterionFromEventFlow
        (uniformLimitCauchyCriterionToEventFlow x) = some x
    exact uniformLimitCauchyCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitCauchyCriterionToEventFlow_injective heq)

theorem UniformLimitCauchyCriterionCarrier_namecert_obligations
    (x : UniformLimitCauchyCriterionUp) :
    ∃ localCert : BHist,
      SemanticNameCert
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ uniformLimitCauchyCriterionFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ uniformLimitCauchyCriterionFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ uniformLimitCauchyCriterionFields x)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk F W M S R E H C P localCert =>
      refine ⟨localCert, ?_⟩
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact
          ⟨localCert, hsame_refl localCert,
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <|
                        List.Mem.tail _ <|
                          List.Mem.tail _ <|
                            List.Mem.tail _ <| List.Mem.head _⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' same₁ same₂
        exact hsame_trans same₁ same₂
      · intro _row _row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      · intro _row source
        exact source
      · intro _row source
        exact source

end BEDC.Derived.UniformLimitCauchyCriterionUp
