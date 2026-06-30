import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteModulusRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteModulusRealUp : Type where
  | mk (S R D M E H C P N : BHist) : FiniteModulusRealUp
  deriving DecidableEq

def finiteModulusRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteModulusRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteModulusRealEncodeBHist h

def finiteModulusRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteModulusRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteModulusRealDecodeBHist tail)

private theorem finiteModulusRealDecode_encode_bhist :
    ∀ h : BHist, finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteModulusRealFields : FiniteModulusRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteModulusRealUp.mk S R D M E H C P N => [S, R, D, M, E, H, C, P, N]

def finiteModulusRealToEventFlow : FiniteModulusRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteModulusRealFields x).map finiteModulusRealEncodeBHist

private def finiteModulusRealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => finiteModulusRealRawAt n rest

private def finiteModulusRealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => finiteModulusRealLengthEq n rest

def finiteModulusRealFromEventFlow : EventFlow → Option FiniteModulusRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match finiteModulusRealLengthEq 9 flow with
      | true =>
          some
            (FiniteModulusRealUp.mk
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 0 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 1 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 2 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 3 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 4 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 5 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 6 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 7 flow))
              (finiteModulusRealDecodeBHist (finiteModulusRealRawAt 8 flow)))
      | false => none

private theorem finiteModulusReal_mk_decode_eq (S R D M E H C P N : BHist) :
    FiniteModulusRealUp.mk
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist S))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist R))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist D))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist M))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N)) =
      FiniteModulusRealUp.mk S R D M E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  have hS := finiteModulusRealDecode_encode_bhist S
  have hR := finiteModulusRealDecode_encode_bhist R
  have hD := finiteModulusRealDecode_encode_bhist D
  have hM := finiteModulusRealDecode_encode_bhist M
  have hE := finiteModulusRealDecode_encode_bhist E
  have hH := finiteModulusRealDecode_encode_bhist H
  have hC := finiteModulusRealDecode_encode_bhist C
  have hP := finiteModulusRealDecode_encode_bhist P
  have hN := finiteModulusRealDecode_encode_bhist N
  exact
    Eq.trans
      (congrArg
        (fun z =>
          FiniteModulusRealUp.mk z
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist R))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist D))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist M))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hS)
      (Eq.trans
        (congrArg
          (fun z =>
            FiniteModulusRealUp.mk S z
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist D))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist M))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hR)
        (Eq.trans
          (congrArg
            (fun z =>
              FiniteModulusRealUp.mk S R z
                (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist M))
                (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
                (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
                (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
                (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
                (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hD)
          (Eq.trans
            (congrArg
              (fun z =>
                FiniteModulusRealUp.mk S R D z
                  (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
                  (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
                  (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
                  (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
                  (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hM)
            (Eq.trans
              (congrArg
                (fun z =>
                  FiniteModulusRealUp.mk S R D M z
                    (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
                    (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
                    (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
                    (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hE)
              (Eq.trans
                (congrArg
                  (fun z =>
                    FiniteModulusRealUp.mk S R D M E z
                      (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
                      (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
                      (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hH)
                (Eq.trans
                  (congrArg
                    (fun z =>
                      FiniteModulusRealUp.mk S R D M E H z
                        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
                        (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hC)
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        FiniteModulusRealUp.mk S R D M E H C z
                          (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) hP)
                    (congrArg (fun z => FiniteModulusRealUp.mk S R D M E H C P z) hN))))))))

private theorem finiteModulusReal_round_trip (x : FiniteModulusRealUp) :
    finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R D M E H C P N =>
      change
        some
          (FiniteModulusRealUp.mk
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist S))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist R))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist D))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist M))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
            (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) =
          some (FiniteModulusRealUp.mk S R D M E H C P N)
      exact congrArg some (finiteModulusReal_mk_decode_eq S R D M E H C P N)

private theorem finiteModulusRealToEventFlow_injective {x y : FiniteModulusRealUp} :
    finiteModulusRealToEventFlow x = finiteModulusRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow x) =
        finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow y) :=
    congrArg finiteModulusRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteModulusReal_round_trip x).symm
      (Eq.trans hread (finiteModulusReal_round_trip y)))

private theorem finiteModulusReal_fields_faithful :
    ∀ x y : FiniteModulusRealUp, finiteModulusRealFields x = finiteModulusRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S R D M E H C P N =>
      cases y with
      | mk S' R' D' M' E' H' C' P' N' =>
          injection hfields with hS tail0
          injection tail0 with hR tail1
          injection tail1 with hD tail2
          injection tail2 with hM tail3
          injection tail3 with hE tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hS
          subst hR
          subst hD
          subst hM
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance finiteModulusRealBHistCarrier : BHistCarrier FiniteModulusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteModulusRealToEventFlow
  fromEventFlow := finiteModulusRealFromEventFlow

instance finiteModulusRealChapterTasteGate : ChapterTasteGate FiniteModulusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow x) = some x
    exact finiteModulusReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteModulusRealToEventFlow_injective heq)

instance finiteModulusRealFieldFaithful : FieldFaithful FiniteModulusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteModulusRealFields
  field_faithful := finiteModulusReal_fields_faithful

instance finiteModulusRealNontrivial : Nontrivial FiniteModulusRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteModulusRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteModulusRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteModulusRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteModulusRealChapterTasteGate

theorem FiniteModulusRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist h) = h) ∧
      (∀ x : FiniteModulusRealUp,
        finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow x) = some x) ∧
        (∀ x y : FiniteModulusRealUp,
          finiteModulusRealToEventFlow x = finiteModulusRealToEventFlow y → x = y) ∧
          finiteModulusRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  have decode :
      ∀ h : BHist, finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have round :
      ∀ x : FiniteModulusRealUp,
        finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow x) = some x := by
    intro x
    cases x with
    | mk S R D M E H C P N =>
        change
          some
            (FiniteModulusRealUp.mk
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist S))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist R))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist D))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist M))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist E))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist H))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist C))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist P))
              (finiteModulusRealDecodeBHist (finiteModulusRealEncodeBHist N))) =
            some (FiniteModulusRealUp.mk S R D M E H C P N)
        exact congrArg some (finiteModulusReal_mk_decode_eq S R D M E H C P N)
  have injective :
      ∀ x y : FiniteModulusRealUp,
        finiteModulusRealToEventFlow x = finiteModulusRealToEventFlow y → x = y := by
    intro x y heq
    have hread :
        finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow x) =
          finiteModulusRealFromEventFlow (finiteModulusRealToEventFlow y) :=
      congrArg finiteModulusRealFromEventFlow heq
    exact Option.some.inj (Eq.trans (round x).symm (Eq.trans hread (round y)))
  exact ⟨decode, round, injective, rfl⟩

end BEDC.Derived.FiniteModulusRealUp
