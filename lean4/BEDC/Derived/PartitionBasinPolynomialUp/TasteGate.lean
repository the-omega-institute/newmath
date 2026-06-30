import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PartitionBasinPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PartitionBasinPolynomialUp : Type where
  | mk (M S D E F Q I T H C P N : BHist) : PartitionBasinPolynomialUp
  deriving DecidableEq

def partitionBasinPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: partitionBasinPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: partitionBasinPolynomialEncodeBHist h

def partitionBasinPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (partitionBasinPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (partitionBasinPolynomialDecodeBHist tail)

private theorem partitionBasinPolynomialDecode_encode_bhist :
    ∀ h : BHist,
      partitionBasinPolynomialDecodeBHist
        (partitionBasinPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def partitionBasinPolynomialFields : PartitionBasinPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PartitionBasinPolynomialUp.mk M S D E F Q I T H C P N =>
      [M, S, D, E, F, Q, I, T, H, C, P, N]

def partitionBasinPolynomialToEventFlow : PartitionBasinPolynomialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (partitionBasinPolynomialFields x).map partitionBasinPolynomialEncodeBHist

private def partitionBasinPolynomialEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => partitionBasinPolynomialEventAtDefault index rest

def partitionBasinPolynomialFromEventFlow
    (ef : EventFlow) : Option PartitionBasinPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PartitionBasinPolynomialUp.mk
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 0 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 1 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 2 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 3 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 4 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 5 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 6 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 7 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 8 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 9 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 10 ef))
      (partitionBasinPolynomialDecodeBHist (partitionBasinPolynomialEventAtDefault 11 ef)))

private theorem partitionBasinPolynomial_mk_congr
    {M M' S S' D D' E E' F F' Q Q' I I' T T' H H' C C' P P' N N' : BHist}
    (hM : M' = M) (hS : S' = S) (hD : D' = D) (hE : E' = E)
    (hF : F' = F) (hQ : Q' = Q) (hI : I' = I) (hT : T' = T)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    PartitionBasinPolynomialUp.mk M' S' D' E' F' Q' I' T' H' C' P' N' =
      PartitionBasinPolynomialUp.mk M S D E F Q I T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hS
  cases hD
  cases hE
  cases hF
  cases hQ
  cases hI
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem partitionBasinPolynomial_round_trip :
    ∀ x : PartitionBasinPolynomialUp,
      partitionBasinPolynomialFromEventFlow
        (partitionBasinPolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S D E F Q I T H C P N =>
      exact
        congrArg some
          (partitionBasinPolynomial_mk_congr
            (partitionBasinPolynomialDecode_encode_bhist M)
            (partitionBasinPolynomialDecode_encode_bhist S)
            (partitionBasinPolynomialDecode_encode_bhist D)
            (partitionBasinPolynomialDecode_encode_bhist E)
            (partitionBasinPolynomialDecode_encode_bhist F)
            (partitionBasinPolynomialDecode_encode_bhist Q)
            (partitionBasinPolynomialDecode_encode_bhist I)
            (partitionBasinPolynomialDecode_encode_bhist T)
            (partitionBasinPolynomialDecode_encode_bhist H)
            (partitionBasinPolynomialDecode_encode_bhist C)
            (partitionBasinPolynomialDecode_encode_bhist P)
            (partitionBasinPolynomialDecode_encode_bhist N))

private theorem partitionBasinPolynomialToEventFlow_injective
    {x y : PartitionBasinPolynomialUp} :
    partitionBasinPolynomialToEventFlow x =
      partitionBasinPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      partitionBasinPolynomialFromEventFlow (partitionBasinPolynomialToEventFlow x) =
        partitionBasinPolynomialFromEventFlow (partitionBasinPolynomialToEventFlow y) :=
    congrArg partitionBasinPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (partitionBasinPolynomial_round_trip x).symm
      (Eq.trans hread (partitionBasinPolynomial_round_trip y)))

instance partitionBasinPolynomialBHistCarrier : BHistCarrier PartitionBasinPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := partitionBasinPolynomialToEventFlow
  fromEventFlow := partitionBasinPolynomialFromEventFlow

instance partitionBasinPolynomialChapterTasteGate :
    ChapterTasteGate PartitionBasinPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      partitionBasinPolynomialFromEventFlow
        (partitionBasinPolynomialToEventFlow x) = some x
    exact partitionBasinPolynomial_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (partitionBasinPolynomialToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PartitionBasinPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  partitionBasinPolynomialChapterTasteGate

theorem PartitionBasinPolynomialTasteGate_single_carrier_alignment :
    (forall h : BHist,
      partitionBasinPolynomialDecodeBHist
        (partitionBasinPolynomialEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PartitionBasinPolynomialUp) ∧
        Nonempty (ChapterTasteGate PartitionBasinPolynomialUp) ∧
          partitionBasinPolynomialEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨partitionBasinPolynomialDecode_encode_bhist,
      ⟨partitionBasinPolynomialBHistCarrier⟩,
      ⟨partitionBasinPolynomialChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PartitionBasinPolynomialUp
