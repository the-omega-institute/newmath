import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorCylinderBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorCylinderBasisUp : Type where
  | mk (C S W B L R H K P N : BHist) : CantorCylinderBasisUp
  deriving DecidableEq

def cantorCylinderBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorCylinderBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorCylinderBasisEncodeBHist h

def cantorCylinderBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorCylinderBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorCylinderBasisDecodeBHist tail)

private theorem CantorCylinderBasisTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorCylinderBasisFields : CantorCylinderBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorCylinderBasisUp.mk C S W B L R H K P N => [C, S, W, B, L, R, H, K, P, N]

def cantorCylinderBasisToEventFlow : CantorCylinderBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cantorCylinderBasisEncodeBHist (cantorCylinderBasisFields x)

private def cantorCylinderBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorCylinderBasisEventAtDefault index rest

def cantorCylinderBasisFromEventFlow
    (ef : EventFlow) : Option CantorCylinderBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CantorCylinderBasisUp.mk
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 0 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 1 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 2 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 3 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 4 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 5 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 6 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 7 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 8 ef))
      (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEventAtDefault 9 ef)))

private theorem CantorCylinderBasisTasteGate_single_carrier_alignment_mk_congr
    {C C' S S' W W' B B' L L' R R' H H' K K' P P' N N' : BHist}
    (hC : C' = C) (hS : S' = S) (hW : W' = W) (hB : B' = B)
    (hL : L' = L) (hR : R' = R) (hH : H' = H) (hK : K' = K)
    (hP : P' = P) (hN : N' = N) :
    CantorCylinderBasisUp.mk C' S' W' B' L' R' H' K' P' N' =
      CantorCylinderBasisUp.mk C S W B L R H K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hS
  cases hW
  cases hB
  cases hL
  cases hR
  cases hH
  cases hK
  cases hP
  cases hN
  rfl

private theorem CantorCylinderBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CantorCylinderBasisUp,
      cantorCylinderBasisFromEventFlow (cantorCylinderBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C S W B L R H K P N =>
      change
        some
          (CantorCylinderBasisUp.mk
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist C))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist S))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist W))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist B))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist L))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist R))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist H))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist K))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist P))
            (cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist N))) =
          some (CantorCylinderBasisUp.mk C S W B L R H K P N)
      exact congrArg some
        (CantorCylinderBasisTasteGate_single_carrier_alignment_mk_congr
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode C)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode S)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode W)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode B)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode L)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode R)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode H)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode K)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode P)
          (CantorCylinderBasisTasteGate_single_carrier_alignment_decode N))

private theorem CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective
    {h k : BHist} :
    cantorCylinderBasisEncodeBHist h = cantorCylinderBasisEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist h) =
        cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist k) :=
    congrArg cantorCylinderBasisDecodeBHist heq
  exact Eq.trans
    (CantorCylinderBasisTasteGate_single_carrier_alignment_decode h).symm
    (Eq.trans hdecode (CantorCylinderBasisTasteGate_single_carrier_alignment_decode k))

private theorem CantorCylinderBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorCylinderBasisUp} :
    cantorCylinderBasisToEventFlow x = cantorCylinderBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk C1 S1 W1 B1 L1 R1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 S2 W2 B2 L2 R2 H2 K2 P2 N2 =>
          change
            [cantorCylinderBasisEncodeBHist C1, cantorCylinderBasisEncodeBHist S1,
              cantorCylinderBasisEncodeBHist W1, cantorCylinderBasisEncodeBHist B1,
              cantorCylinderBasisEncodeBHist L1, cantorCylinderBasisEncodeBHist R1,
              cantorCylinderBasisEncodeBHist H1, cantorCylinderBasisEncodeBHist K1,
              cantorCylinderBasisEncodeBHist P1, cantorCylinderBasisEncodeBHist N1] =
            [cantorCylinderBasisEncodeBHist C2, cantorCylinderBasisEncodeBHist S2,
              cantorCylinderBasisEncodeBHist W2, cantorCylinderBasisEncodeBHist B2,
              cantorCylinderBasisEncodeBHist L2, cantorCylinderBasisEncodeBHist R2,
              cantorCylinderBasisEncodeBHist H2, cantorCylinderBasisEncodeBHist K2,
              cantorCylinderBasisEncodeBHist P2, cantorCylinderBasisEncodeBHist N2] at heq
          injection heq with hC tailC
          injection tailC with hS tailS
          injection tailS with hW tailW
          injection tailW with hB tailB
          injection tailB with hL tailL
          injection tailL with hR tailR
          injection tailR with hH tailH
          injection tailH with hK tailK
          injection tailK with hP tailP
          injection tailP with hN _
          exact
            CantorCylinderBasisTasteGate_single_carrier_alignment_mk_congr
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hC)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hS)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hW)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hB)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hL)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hR)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hH)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hK)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hP)
              (CantorCylinderBasisTasteGate_single_carrier_alignment_encode_injective hN)

private theorem CantorCylinderBasisTasteGate_single_carrier_alignment_fields :
    ∀ x y : CantorCylinderBasisUp,
      cantorCylinderBasisFields x = cantorCylinderBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C1 S1 W1 B1 L1 R1 H1 K1 P1 N1 =>
      cases y with
      | mk C2 S2 W2 B2 L2 R2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance cantorCylinderBasisBHistCarrier :
    BHistCarrier CantorCylinderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorCylinderBasisToEventFlow
  fromEventFlow := cantorCylinderBasisFromEventFlow

instance cantorCylinderBasisChapterTasteGate :
    ChapterTasteGate CantorCylinderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorCylinderBasisFromEventFlow (cantorCylinderBasisToEventFlow x) = some x
    exact CantorCylinderBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CantorCylinderBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cantorCylinderBasisFieldFaithful :
    FieldFaithful CantorCylinderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorCylinderBasisFields
  field_faithful := CantorCylinderBasisTasteGate_single_carrier_alignment_fields

instance cantorCylinderBasisNontrivial :
    Nontrivial CantorCylinderBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorCylinderBasisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorCylinderBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CantorCylinderBasisTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CantorCylinderBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorCylinderBasisChapterTasteGate

theorem CantorCylinderBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cantorCylinderBasisDecodeBHist (cantorCylinderBasisEncodeBHist h) = h) ∧
      (∀ x : CantorCylinderBasisUp,
        cantorCylinderBasisFromEventFlow (cantorCylinderBasisToEventFlow x) = some x) ∧
        (∀ x y : CantorCylinderBasisUp,
          cantorCylinderBasisToEventFlow x = cantorCylinderBasisToEventFlow y → x = y) ∧
          cantorCylinderBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CantorCylinderBasisTasteGate_single_carrier_alignment_decode,
      CantorCylinderBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CantorCylinderBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CantorCylinderBasisUp
