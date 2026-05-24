import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDyadicEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDyadicEmbeddingUp : Type where
  | mk (D S R E H C P N : BHist) : RealDyadicEmbeddingUp
  deriving DecidableEq

def realDyadicEmbeddingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDyadicEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDyadicEmbeddingEncodeBHist h

def realDyadicEmbeddingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDyadicEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDyadicEmbeddingDecodeBHist tail)

private theorem realDyadicEmbedding_decode_encode_bhist :
    forall h : BHist, realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realDyadicEmbeddingFields : RealDyadicEmbeddingUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealDyadicEmbeddingUp.mk D S R E H C P N => [D, S, R, E, H, C, P, N]

def realDyadicEmbeddingToEventFlow : RealDyadicEmbeddingUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realDyadicEmbeddingFields x).map realDyadicEmbeddingEncodeBHist

private def realDyadicEmbeddingEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realDyadicEmbeddingEventAtDefault index rest

def realDyadicEmbeddingFromEventFlow (ef : EventFlow) : Option RealDyadicEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealDyadicEmbeddingUp.mk
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 0 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 1 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 2 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 3 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 4 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 5 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 6 ef))
      (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEventAtDefault 7 ef)))

private theorem realDyadicEmbedding_round_trip :
    forall x : RealDyadicEmbeddingUp,
      realDyadicEmbeddingFromEventFlow (realDyadicEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E H C P N =>
      change
        some
          (RealDyadicEmbeddingUp.mk
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist D))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist S))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist R))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist E))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist H))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist C))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist P))
            (realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist N))) =
          some (RealDyadicEmbeddingUp.mk D S R E H C P N)
      rw [realDyadicEmbedding_decode_encode_bhist D,
        realDyadicEmbedding_decode_encode_bhist S,
        realDyadicEmbedding_decode_encode_bhist R,
        realDyadicEmbedding_decode_encode_bhist E,
        realDyadicEmbedding_decode_encode_bhist H,
        realDyadicEmbedding_decode_encode_bhist C,
        realDyadicEmbedding_decode_encode_bhist P,
        realDyadicEmbedding_decode_encode_bhist N]

private theorem realDyadicEmbeddingToEventFlow_injective {x y : RealDyadicEmbeddingUp} :
    realDyadicEmbeddingToEventFlow x = realDyadicEmbeddingToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realDyadicEmbeddingFromEventFlow (realDyadicEmbeddingToEventFlow x) =
        realDyadicEmbeddingFromEventFlow (realDyadicEmbeddingToEventFlow y) :=
    congrArg realDyadicEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realDyadicEmbedding_round_trip x).symm
      (Eq.trans hread (realDyadicEmbedding_round_trip y)))

instance realDyadicEmbeddingBHistCarrier : BHistCarrier RealDyadicEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDyadicEmbeddingToEventFlow
  fromEventFlow := realDyadicEmbeddingFromEventFlow

instance realDyadicEmbeddingChapterTasteGate : ChapterTasteGate RealDyadicEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realDyadicEmbeddingFromEventFlow (realDyadicEmbeddingToEventFlow x) = some x
    exact realDyadicEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realDyadicEmbeddingToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealDyadicEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realDyadicEmbeddingChapterTasteGate

theorem RealDyadicEmbeddingTasteGate_single_carrier_alignment :
    (forall h : BHist, realDyadicEmbeddingDecodeBHist (realDyadicEmbeddingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealDyadicEmbeddingUp) ∧
        Nonempty (ChapterTasteGate RealDyadicEmbeddingUp) ∧
          realDyadicEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realDyadicEmbedding_decode_encode_bhist,
      ⟨realDyadicEmbeddingBHistCarrier⟩,
      ⟨realDyadicEmbeddingChapterTasteGate⟩,
      rfl⟩

def RealDyadicEmbeddingCarrier [AskSetup] [PackageSetup]
    (D S R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont D S R ∧ Cont R E H ∧ Cont H C P ∧ PkgSig bundle N pkg

theorem RealDyadicEmbeddingCarrier_regseq_handoff [AskSetup] [PackageSetup]
    {D S R E H C P N realRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealDyadicEmbeddingCarrier D S R E H C P N bundle pkg ->
      Cont R E realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧
            UnaryHistory realRead ∧ Cont D S R ∧ Cont R E realRead ∧
              PkgSig bundle N pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier realRoute realPkg
  obtain ⟨DUnary, SUnary, RUnary, EUnary, _HUnary, _CUnary, _PUnary, _NUnary,
    dsRoute, _reRoute, _hcRoute, namePkg⟩ := carrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed RUnary EUnary realRoute
  exact
    ⟨DUnary, SUnary, RUnary, EUnary, realUnary, dsRoute, realRoute, namePkg, realPkg⟩

end BEDC.Derived.RealDyadicEmbeddingUp
