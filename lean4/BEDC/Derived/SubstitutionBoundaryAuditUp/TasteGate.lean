import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubstitutionBoundaryAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubstitutionBoundaryAuditUp : Type where
  | mk :
      (T V d Csrc Cval Q R L E H C P N : BHist) →
        SubstitutionBoundaryAuditUp
  deriving DecidableEq

def substitutionBoundaryAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: substitutionBoundaryAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: substitutionBoundaryAuditEncodeBHist h

def substitutionBoundaryAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (substitutionBoundaryAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (substitutionBoundaryAuditDecodeBHist tail)

private theorem substitutionBoundaryAudit_decode_encode_bhist :
    ∀ h : BHist,
      substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def substitutionBoundaryAuditToEventFlow : SubstitutionBoundaryAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubstitutionBoundaryAuditUp.mk T V d Csrc Cval Q R L E H C P N =>
      [[BMark.b0],
        substitutionBoundaryAuditEncodeBHist T,
        [BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist Csrc,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist Cval,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        substitutionBoundaryAuditEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionBoundaryAuditEncodeBHist N]

private def substitutionBoundaryAuditRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => substitutionBoundaryAuditRawAt n rest

private def substitutionBoundaryAuditLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => substitutionBoundaryAuditLengthEq n rest

def substitutionBoundaryAuditFromEventFlow : EventFlow → Option SubstitutionBoundaryAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match substitutionBoundaryAuditLengthEq 26 flow with
      | true =>
          some
            (SubstitutionBoundaryAuditUp.mk
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 1 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 3 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 5 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 7 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 9 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 11 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 13 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 15 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 17 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 19 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 21 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 23 flow))
              (substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditRawAt 25 flow)))
      | false => none

private theorem substitutionBoundaryAudit_round_trip :
    ∀ x : SubstitutionBoundaryAuditUp,
      substitutionBoundaryAuditFromEventFlow (substitutionBoundaryAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T V d Csrc Cval Q R L E H C P N =>
      change
        some
          (SubstitutionBoundaryAuditUp.mk
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist T))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist V))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist d))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist Csrc))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist Cval))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist Q))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist R))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist L))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist E))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist H))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist C))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist P))
            (substitutionBoundaryAuditDecodeBHist
              (substitutionBoundaryAuditEncodeBHist N))) =
          some (SubstitutionBoundaryAuditUp.mk T V d Csrc Cval Q R L E H C P N)
      rw [substitutionBoundaryAudit_decode_encode_bhist T,
        substitutionBoundaryAudit_decode_encode_bhist V,
        substitutionBoundaryAudit_decode_encode_bhist d,
        substitutionBoundaryAudit_decode_encode_bhist Csrc,
        substitutionBoundaryAudit_decode_encode_bhist Cval,
        substitutionBoundaryAudit_decode_encode_bhist Q,
        substitutionBoundaryAudit_decode_encode_bhist R,
        substitutionBoundaryAudit_decode_encode_bhist L,
        substitutionBoundaryAudit_decode_encode_bhist E,
        substitutionBoundaryAudit_decode_encode_bhist H,
        substitutionBoundaryAudit_decode_encode_bhist C,
        substitutionBoundaryAudit_decode_encode_bhist P,
        substitutionBoundaryAudit_decode_encode_bhist N]

private theorem substitutionBoundaryAuditToEventFlow_injective
    {x y : SubstitutionBoundaryAuditUp} :
    substitutionBoundaryAuditToEventFlow x = substitutionBoundaryAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      substitutionBoundaryAuditFromEventFlow (substitutionBoundaryAuditToEventFlow x) =
        substitutionBoundaryAuditFromEventFlow (substitutionBoundaryAuditToEventFlow y) :=
    congrArg substitutionBoundaryAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (substitutionBoundaryAudit_round_trip x).symm
      (Eq.trans hread (substitutionBoundaryAudit_round_trip y)))

instance substitutionBoundaryAuditBHistCarrier : BHistCarrier SubstitutionBoundaryAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := substitutionBoundaryAuditToEventFlow
  fromEventFlow := substitutionBoundaryAuditFromEventFlow

instance substitutionBoundaryAuditChapterTasteGate :
    ChapterTasteGate SubstitutionBoundaryAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change substitutionBoundaryAuditFromEventFlow (substitutionBoundaryAuditToEventFlow x) = some x
    exact substitutionBoundaryAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (substitutionBoundaryAuditToEventFlow_injective heq)

instance substitutionBoundaryAuditFieldFaithful : FieldFaithful SubstitutionBoundaryAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubstitutionBoundaryAuditUp.mk T V d Csrc Cval Q R L E H C P N =>
        [T, V, d, Csrc, Cval, Q, R, L, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk T1 V1 d1 Csrc1 Cval1 Q1 R1 L1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk T2 V2 d2 Csrc2 Cval2 Q2 R2 L2 E2 H2 C2 P2 N2 =>
            cases h
            rfl

instance substitutionBoundaryAuditNontrivial : Nontrivial SubstitutionBoundaryAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubstitutionBoundaryAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SubstitutionBoundaryAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubstitutionBoundaryAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  substitutionBoundaryAuditChapterTasteGate

theorem SubstitutionBoundaryAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      substitutionBoundaryAuditDecodeBHist (substitutionBoundaryAuditEncodeBHist h) = h) ∧
      (∀ x : SubstitutionBoundaryAuditUp,
        substitutionBoundaryAuditFromEventFlow (substitutionBoundaryAuditToEventFlow x) = some x) ∧
        (∀ x y : SubstitutionBoundaryAuditUp,
          substitutionBoundaryAuditToEventFlow x =
            substitutionBoundaryAuditToEventFlow y → x = y) ∧
          substitutionBoundaryAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨substitutionBoundaryAudit_decode_encode_bhist,
      substitutionBoundaryAudit_round_trip,
      by
        intro x y heq
        exact substitutionBoundaryAuditToEventFlow_injective heq,
      rfl⟩

theorem SubstitutionBoundaryAuditCarrier_falsifiable_route
    {T V d Csrc Cval Q R L E H C P N T' V' d' Csrc' Cval' Q' R' L' E' H' C'
      P' N' : BHist}
    (heq :
      substitutionBoundaryAuditToEventFlow
          (SubstitutionBoundaryAuditUp.mk T V d Csrc Cval Q R L E H C P N) =
        substitutionBoundaryAuditToEventFlow
          (SubstitutionBoundaryAuditUp.mk T' V' d' Csrc' Cval' Q' R' L' E' H' C'
            P' N'))
    (hshift : Cont Csrc L Q) (hsub : Cont Cval L R) :
    hsame Csrc Csrc' ∧ hsame Cval Cval' ∧ hsame L L' ∧ hsame Q Q' ∧
      hsame R R' ∧ Cont Csrc' L' Q' ∧ Cont Cval' L' R' := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  have hmk :=
    substitutionBoundaryAuditToEventFlow_injective
      (x := SubstitutionBoundaryAuditUp.mk T V d Csrc Cval Q R L E H C P N)
      (y := SubstitutionBoundaryAuditUp.mk T' V' d' Csrc' Cval' Q' R' L' E' H' C'
        P' N')
      heq
  cases hmk
  exact
    ⟨hsame_refl Csrc, hsame_refl Cval, hsame_refl L, hsame_refl Q, hsame_refl R,
      hshift, hsub⟩

end BEDC.Derived.SubstitutionBoundaryAuditUp
