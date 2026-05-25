import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RieszMarkovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RieszMarkovUp : Type where
  | mk (K F L M I H C P N : BHist) : RieszMarkovUp
  deriving DecidableEq

def rieszMarkovEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rieszMarkovEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rieszMarkovEncodeBHist h

def rieszMarkovDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rieszMarkovDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rieszMarkovDecodeBHist tail)

private theorem RieszMarkovTasteGate_single_carrier_alignment_decode :
    forall h : BHist, rieszMarkovDecodeBHist (rieszMarkovEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rieszMarkovToEventFlow : RieszMarkovUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RieszMarkovUp.mk K F L M I H C P N =>
      [rieszMarkovEncodeBHist K,
        rieszMarkovEncodeBHist F,
        rieszMarkovEncodeBHist L,
        rieszMarkovEncodeBHist M,
        rieszMarkovEncodeBHist I,
        rieszMarkovEncodeBHist H,
        rieszMarkovEncodeBHist C,
        rieszMarkovEncodeBHist P,
        rieszMarkovEncodeBHist N]

private def rieszMarkovEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rieszMarkovEventAtDefault index rest

def rieszMarkovFromEventFlow (ef : EventFlow) : Option RieszMarkovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RieszMarkovUp.mk
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 0 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 1 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 2 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 3 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 4 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 5 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 6 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 7 ef))
      (rieszMarkovDecodeBHist (rieszMarkovEventAtDefault 8 ef)))

private theorem RieszMarkovTasteGate_single_carrier_alignment_round_trip :
    forall x : RieszMarkovUp,
      rieszMarkovFromEventFlow (rieszMarkovToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F L M I H C P N =>
      change
        some
          (RieszMarkovUp.mk
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist K))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist F))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist L))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist M))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist I))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist H))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist C))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist P))
            (rieszMarkovDecodeBHist (rieszMarkovEncodeBHist N))) =
          some (RieszMarkovUp.mk K F L M I H C P N)
      rw [RieszMarkovTasteGate_single_carrier_alignment_decode K,
        RieszMarkovTasteGate_single_carrier_alignment_decode F,
        RieszMarkovTasteGate_single_carrier_alignment_decode L,
        RieszMarkovTasteGate_single_carrier_alignment_decode M,
        RieszMarkovTasteGate_single_carrier_alignment_decode I,
        RieszMarkovTasteGate_single_carrier_alignment_decode H,
        RieszMarkovTasteGate_single_carrier_alignment_decode C,
        RieszMarkovTasteGate_single_carrier_alignment_decode P,
        RieszMarkovTasteGate_single_carrier_alignment_decode N]

private theorem RieszMarkovTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RieszMarkovUp} :
    rieszMarkovToEventFlow x = rieszMarkovToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rieszMarkovFromEventFlow (rieszMarkovToEventFlow x) =
        rieszMarkovFromEventFlow (rieszMarkovToEventFlow y) :=
    congrArg rieszMarkovFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RieszMarkovTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RieszMarkovTasteGate_single_carrier_alignment_round_trip y)))

private def rieszMarkovFields : RieszMarkovUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RieszMarkovUp.mk K F L M I H C P N => [K, F, L, M, I, H, C, P, N]

private theorem RieszMarkovTasteGate_single_carrier_alignment_fields :
    forall x y : RieszMarkovUp, rieszMarkovFields x = rieszMarkovFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 L1 M1 I1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 L2 M2 I2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance rieszMarkovBHistCarrier : BHistCarrier RieszMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rieszMarkovToEventFlow
  fromEventFlow := rieszMarkovFromEventFlow

instance rieszMarkovChapterTasteGate : ChapterTasteGate RieszMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rieszMarkovFromEventFlow (rieszMarkovToEventFlow x) = some x
    exact RieszMarkovTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RieszMarkovTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rieszMarkovFieldFaithful : FieldFaithful RieszMarkovUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rieszMarkovFields
  field_faithful := RieszMarkovTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate RieszMarkovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rieszMarkovChapterTasteGate

theorem RieszMarkovTasteGate_single_carrier_alignment :
    (forall h : BHist, rieszMarkovDecodeBHist (rieszMarkovEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RieszMarkovUp) ∧
        Nonempty (ChapterTasteGate RieszMarkovUp) ∧
          Nonempty (FieldFaithful RieszMarkovUp) ∧
            rieszMarkovEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨RieszMarkovTasteGate_single_carrier_alignment_decode,
      ⟨rieszMarkovBHistCarrier⟩,
      ⟨rieszMarkovChapterTasteGate⟩,
      ⟨rieszMarkovFieldFaithful⟩,
      rfl⟩

def RieszMarkovCarrier [AskSetup] [PackageSetup]
    (K F L M I H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont K F L ∧ Cont M I C ∧ hsame H H ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RieszMarkovCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K F L M I H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RieszMarkovCarrier K F L M I H C P N bundle pkg →
      SemanticNameCert
        (fun row : BHist => RieszMarkovCarrier K F L M I H C P N bundle pkg ∧ hsame row N)
        (fun _row : BHist =>
          RieszMarkovCarrier K F L M I H C P N bundle pkg ∧ Cont K F L ∧ Cont M I C)
        (fun row : BHist => PkgSig bundle N pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  have hcarrier := carrier
  obtain ⟨compactObservableFunctional, measureIntegralReplay, _transportSelf, _provenancePkg,
    namePkg⟩ := carrier
  constructor
  · constructor
    · exact ⟨N, hcarrier, hsame_refl N⟩
    · intro row _source
      exact hsame_refl row
    · intro row other sameRows
      exact hsame_symm sameRows
    · intro row middle other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row other sameRows source
      exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row _source
    exact ⟨hcarrier, compactObservableFunctional, measureIntegralReplay⟩
  · intro _row source
    exact ⟨namePkg, source.right⟩

end BEDC.Derived.RieszMarkovUp
