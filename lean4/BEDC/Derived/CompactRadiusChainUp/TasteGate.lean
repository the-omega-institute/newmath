import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRadiusChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRadiusChainUp : Type where
  | mk (K G B A F D U H C P N : BHist) : CompactRadiusChainUp
  deriving DecidableEq

def compactRadiusChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRadiusChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRadiusChainEncodeBHist h

def compactRadiusChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRadiusChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRadiusChainDecodeBHist tail)

private theorem compactRadiusChainDecode_encode :
    ∀ h : BHist, compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRadiusChainFields : CompactRadiusChainUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRadiusChainUp.mk K G B A F D U H C P N => [K, G, B, A, F, D, U, H, C, P, N]

def compactRadiusChainToEventFlow : CompactRadiusChainUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactRadiusChainFields x).map compactRadiusChainEncodeBHist

private def compactRadiusChainRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactRadiusChainRawAt index rest

def compactRadiusChainFromEventFlow (flow : EventFlow) : Option CompactRadiusChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactRadiusChainUp.mk
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 0 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 1 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 2 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 3 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 4 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 5 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 6 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 7 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 8 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 9 flow))
      (compactRadiusChainDecodeBHist (compactRadiusChainRawAt 10 flow)))

private theorem compactRadiusChain_round_trip (x : CompactRadiusChainUp) :
    compactRadiusChainFromEventFlow (compactRadiusChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K G B A F D U H C P N =>
      change
        some
          (CompactRadiusChainUp.mk
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist K))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist G))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist B))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist A))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist F))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist D))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist U))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist H))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist C))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist P))
            (compactRadiusChainDecodeBHist (compactRadiusChainEncodeBHist N))) =
          some (CompactRadiusChainUp.mk K G B A F D U H C P N)
      rw [compactRadiusChainDecode_encode K, compactRadiusChainDecode_encode G,
        compactRadiusChainDecode_encode B, compactRadiusChainDecode_encode A,
        compactRadiusChainDecode_encode F, compactRadiusChainDecode_encode D,
        compactRadiusChainDecode_encode U, compactRadiusChainDecode_encode H,
        compactRadiusChainDecode_encode C, compactRadiusChainDecode_encode P,
        compactRadiusChainDecode_encode N]

private theorem compactRadiusChainToEventFlow_injective {x y : CompactRadiusChainUp} :
    compactRadiusChainToEventFlow x = compactRadiusChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRadiusChainFromEventFlow (compactRadiusChainToEventFlow x) =
        compactRadiusChainFromEventFlow (compactRadiusChainToEventFlow y) :=
    congrArg compactRadiusChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactRadiusChain_round_trip x).symm
      (Eq.trans hread (compactRadiusChain_round_trip y)))

instance compactRadiusChainBHistCarrier : BHistCarrier CompactRadiusChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRadiusChainToEventFlow
  fromEventFlow := compactRadiusChainFromEventFlow

instance compactRadiusChainChapterTasteGate : ChapterTasteGate CompactRadiusChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactRadiusChainFromEventFlow (compactRadiusChainToEventFlow x) = some x
    exact compactRadiusChain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactRadiusChainToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactRadiusChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactRadiusChainChapterTasteGate

def CompactRadiusChainCarrier [AskSetup] [PackageSetup]
    (K G B A F D U H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory K ∧ UnaryHistory G ∧ UnaryHistory B ∧ UnaryHistory A ∧
    UnaryHistory F ∧ UnaryHistory D ∧ UnaryHistory U ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont K G B ∧
        Cont B A F ∧ Cont F D U ∧ Cont H C N ∧ PkgSig bundle P pkg

theorem CompactRadiusChainCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K G B A F D U H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactRadiusChainCarrier K G B A F D U H C P N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CompactRadiusChainCarrier K G B A F D U H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          CompactRadiusChainCarrier K G B A F D U H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          CompactRadiusChainCarrier K G B A F D U H C P N bundle pkg ∧ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert NameCert BMark
  intro carrier
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact ⟨N, carrier, hsame_refl N⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows source
    exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row source
    exact source
  · intro _row source
    exact source

end BEDC.Derived.CompactRadiusChainUp
