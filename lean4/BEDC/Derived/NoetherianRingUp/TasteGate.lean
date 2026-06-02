import BEDC.Derived.NoetherianRingUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoetherianRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def noetherianRingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noetherianRingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noetherianRingEncodeBHist h

def noetherianRingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noetherianRingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noetherianRingDecodeBHist tail)

def noetherianRingDecideUnaryHistory : (h : BHist) → Decidable (UnaryHistory h)
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => isTrue (by constructor)
  | BHist.e0 _ => isFalse (fun h => h)
  | BHist.e1 h => noetherianRingDecideUnaryHistory h

private theorem noetherianRingDecode_encode_bhist :
    ∀ h : BHist, noetherianRingDecodeBHist (noetherianRingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem noetherianRing_mk_congr
    {C C' I I' A A' G G' H H' Q Q' P P' N N' : BHist}
    (hC : C' = C)
    (hI : I' = I)
    (hA : A' = A)
    (hG : G' = G)
    (hH : H' = H)
    (hQ : Q' = Q)
    (hP : P' = P)
    (hN : N' = N) :
    (unaryN' : UnaryHistory N') →
      (sameN' : hsame N' C') →
        (unaryN : UnaryHistory N) →
          (sameN : hsame N C) →
            NoetherianRingUp.mk C' I' A' G' H' Q' P' N' unaryN' sameN' =
              NoetherianRingUp.mk C I A G H Q P N unaryN sameN := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hI
  cases hA
  cases hG
  cases hH
  cases hQ
  cases hP
  cases hN
  intro unaryN' sameN' unaryN sameN
  have hunary : unaryN' = unaryN := proof_irrel unaryN' unaryN
  have hsameProof : sameN' = sameN := proof_irrel sameN' sameN
  cases hunary
  cases hsameProof
  rfl

def noetherianRingToEventFlow : NoetherianRingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NoetherianRingUp.mk C I A G H Q P N _ _ =>
      [noetherianRingEncodeBHist C,
        noetherianRingEncodeBHist I,
        noetherianRingEncodeBHist A,
        noetherianRingEncodeBHist G,
        noetherianRingEncodeBHist H,
        noetherianRingEncodeBHist Q,
        noetherianRingEncodeBHist P,
        noetherianRingEncodeBHist N]

def noetherianRingFromEventFlow : EventFlow → Option NoetherianRingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | A :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      let cRow := noetherianRingDecodeBHist C
                                      let nRow := noetherianRingDecodeBHist N
                                      match noetherianRingDecideUnaryHistory nRow with
                                      | isFalse _ => none
                                      | isTrue unaryN =>
                                          match (inferInstance : Decidable (nRow = cRow)) with
                                          | isFalse _ => none
                                          | isTrue sameNC =>
                                              some
                                                (NoetherianRingUp.mk
                                                  cRow
                                                  (noetherianRingDecodeBHist I)
                                                  (noetherianRingDecodeBHist A)
                                                  (noetherianRingDecodeBHist G)
                                                  (noetherianRingDecodeBHist H)
                                                  (noetherianRingDecodeBHist Q)
                                                  (noetherianRingDecodeBHist P)
                                                  nRow
                                                  unaryN
                                                  sameNC)
                                  | _ :: _ => none

private theorem noetherianRing_round_trip :
    ∀ x : NoetherianRingUp,
      noetherianRingFromEventFlow (noetherianRingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C I A G H Q P N unaryN sameNC =>
      change
        (let cRow := noetherianRingDecodeBHist (noetherianRingEncodeBHist C)
         let nRow := noetherianRingDecodeBHist (noetherianRingEncodeBHist N)
         match noetherianRingDecideUnaryHistory nRow with
         | isFalse _ => none
         | isTrue unaryN' =>
             match (inferInstance : Decidable (nRow = cRow)) with
             | isFalse _ => none
             | isTrue sameNC' =>
                 some
                   (NoetherianRingUp.mk cRow
                     (noetherianRingDecodeBHist (noetherianRingEncodeBHist I))
                     (noetherianRingDecodeBHist (noetherianRingEncodeBHist A))
                     (noetherianRingDecodeBHist (noetherianRingEncodeBHist G))
                     (noetherianRingDecodeBHist (noetherianRingEncodeBHist H))
                     (noetherianRingDecodeBHist (noetherianRingEncodeBHist Q))
                     (noetherianRingDecodeBHist (noetherianRingEncodeBHist P))
                     nRow unaryN' sameNC')) =
          some (NoetherianRingUp.mk C I A G H Q P N unaryN sameNC)
      rw [noetherianRingDecode_encode_bhist C, noetherianRingDecode_encode_bhist I,
        noetherianRingDecode_encode_bhist A, noetherianRingDecode_encode_bhist G,
        noetherianRingDecode_encode_bhist H, noetherianRingDecode_encode_bhist Q,
        noetherianRingDecode_encode_bhist P, noetherianRingDecode_encode_bhist N]
      cases hUnary : noetherianRingDecideUnaryHistory N with
      | isFalse notUnary =>
          exact False.elim (notUnary unaryN)
      | isTrue unaryN' =>
          cases hSame : (inferInstance : Decidable (N = C)) with
          | isFalse notSame =>
              exact False.elim (notSame sameNC)
          | isTrue sameNC' =>
              simp only [hUnary, hSame]

private theorem noetherianRingToEventFlow_injective {x y : NoetherianRingUp} :
    noetherianRingToEventFlow x = noetherianRingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noetherianRingFromEventFlow (noetherianRingToEventFlow x) =
        noetherianRingFromEventFlow (noetherianRingToEventFlow y) :=
    congrArg noetherianRingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (noetherianRing_round_trip x).symm
      (Eq.trans hread (noetherianRing_round_trip y)))

instance noetherianRingBHistCarrier : BHistCarrier NoetherianRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noetherianRingToEventFlow
  fromEventFlow := noetherianRingFromEventFlow

instance noetherianRingChapterTasteGate : ChapterTasteGate NoetherianRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change noetherianRingFromEventFlow (noetherianRingToEventFlow x) = some x
    exact noetherianRing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (noetherianRingToEventFlow_injective heq)

theorem NoetherianRingTasteGate_single_carrier_alignment :
    (∀ h : BHist, noetherianRingDecodeBHist (noetherianRingEncodeBHist h) = h) ∧
      noetherianRingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact noetherianRingDecode_encode_bhist
  · rfl

end BEDC.Derived.NoetherianRingUp
