import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetrizableSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetrizableSpaceUp : Type where
  | mk (T M B W R E H C P N : BHist) : MetrizableSpaceUp
  deriving DecidableEq

def metrizableSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metrizableSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metrizableSpaceEncodeBHist h

def metrizableSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metrizableSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metrizableSpaceDecodeBHist tail)

private theorem metrizableSpaceDecodeEncode :
    ∀ h : BHist, metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metrizableSpaceFields : MetrizableSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetrizableSpaceUp.mk T M B W R E H C P N => [T, M, B, W, R, E, H, C, P, N]

def metrizableSpaceToEventFlow : MetrizableSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (metrizableSpaceFields x).map metrizableSpaceEncodeBHist

private def metrizableSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metrizableSpaceEventAtDefault index rest

def metrizableSpaceFromEventFlow (ef : EventFlow) : Option MetrizableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetrizableSpaceUp.mk
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 0 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 1 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 2 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 3 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 4 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 5 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 6 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 7 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 8 ef))
      (metrizableSpaceDecodeBHist (metrizableSpaceEventAtDefault 9 ef)))

private theorem metrizableSpaceRoundTrip :
    ∀ x : MetrizableSpaceUp,
      metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M B W R E H C P N =>
      change
        some
          (MetrizableSpaceUp.mk
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist T))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist M))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist B))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist W))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist R))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist E))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist H))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist C))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist P))
            (metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist N))) =
          some (MetrizableSpaceUp.mk T M B W R E H C P N)
      rw [metrizableSpaceDecodeEncode T, metrizableSpaceDecodeEncode M,
        metrizableSpaceDecodeEncode B, metrizableSpaceDecodeEncode W,
        metrizableSpaceDecodeEncode R, metrizableSpaceDecodeEncode E,
        metrizableSpaceDecodeEncode H, metrizableSpaceDecodeEncode C,
        metrizableSpaceDecodeEncode P, metrizableSpaceDecodeEncode N]

private theorem metrizableSpaceToEventFlow_injective {x y : MetrizableSpaceUp} :
    metrizableSpaceToEventFlow x = metrizableSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) =
        metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow y) :=
    congrArg metrizableSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metrizableSpaceRoundTrip x).symm
      (Eq.trans hread (metrizableSpaceRoundTrip y)))

private theorem metrizableSpaceFieldFaithfulProof :
    ∀ x y : MetrizableSpaceUp, metrizableSpaceFields x = metrizableSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T₁ M₁ B₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ M₂ B₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          change
            [T₁, M₁, B₁, W₁, R₁, E₁, H₁, C₁, P₁, N₁] =
              [T₂, M₂, B₂, W₂, R₂, E₂, H₂, C₂, P₂, N₂] at h
          cases h
          rfl

instance metrizableSpaceBHistCarrier : BHistCarrier MetrizableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metrizableSpaceToEventFlow
  fromEventFlow := metrizableSpaceFromEventFlow

instance metrizableSpaceChapterTasteGate : ChapterTasteGate MetrizableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) = some x
    exact metrizableSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metrizableSpaceToEventFlow_injective heq)

instance metrizableSpaceFieldFaithful : FieldFaithful MetrizableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metrizableSpaceFields
  field_faithful := metrizableSpaceFieldFaithfulProof

theorem MetrizableSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MetrizableSpaceUp) ∧
      Nonempty (FieldFaithful MetrizableSpaceUp) ∧
      (∀ h : BHist, metrizableSpaceDecodeBHist (metrizableSpaceEncodeBHist h) = h) ∧
      (∀ x : MetrizableSpaceUp,
        metrizableSpaceFromEventFlow (metrizableSpaceToEventFlow x) = some x) ∧
      (∀ x y : MetrizableSpaceUp,
        metrizableSpaceToEventFlow x = metrizableSpaceToEventFlow y → x = y) ∧
      metrizableSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨metrizableSpaceChapterTasteGate⟩
  constructor
  · exact ⟨metrizableSpaceFieldFaithful⟩
  constructor
  · exact metrizableSpaceDecodeEncode
  constructor
  · exact metrizableSpaceRoundTrip
  constructor
  · intro x y heq
    exact metrizableSpaceToEventFlow_injective heq
  · rfl

theorem MetrizableSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T M B W R E H C P N route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    metrizableSpaceFields (MetrizableSpaceUp.mk T M B W R E H C P N) =
        [T, M, B, W, R, E, H, C, P, N] →
      Cont T B W →
        Cont M W R →
          Cont R E route →
            PkgSig bundle N pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row route ∧
                    ∃ packet : MetrizableSpaceUp,
                      packet = MetrizableSpaceUp.mk T M B W R E H C P N ∧
                        metrizableSpaceFields packet = [T, M, B, W, R, E, H, C, P, N])
                (fun row : BHist => Cont T B W ∧ Cont M W R ∧ Cont R E row)
                (fun row : BHist => hsame row route ∧ PkgSig bundle N pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldsEq topologyWindow metricReadback realRoute pkgSig
  let packet := MetrizableSpaceUp.mk T M B W R E H C P N
  have sourceRoute :
      hsame route route ∧
        ∃ packet : MetrizableSpaceUp,
          packet = MetrizableSpaceUp.mk T M B W R E H C P N ∧
            metrizableSpaceFields packet = [T, M, B, W, R, E, H, C, P, N] :=
    ⟨hsame_refl route, Exists.intro packet ⟨rfl, fieldsEq⟩⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro route sourceRoute
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨topologyWindow, metricReadback, realRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

end BEDC.Derived.MetrizableSpaceUp
