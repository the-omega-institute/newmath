import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactPolishSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactPolishSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K P C S W R H T Q N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory C ∧ UnaryHistory S ∧
      UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory T ∧
        UnaryHistory Q ∧ UnaryHistory N ∧ Cont K W T ∧ Cont P C T ∧
          Cont S R T ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧ UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory C ∧
            UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory H ∧
              UnaryHistory T ∧ UnaryHistory Q ∧ UnaryHistory N ∧ Cont K W T ∧
                Cont P C T ∧ Cont S R T ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle N pkg)
        (fun row : BHist =>
          hsame row N ∧ Cont K W T ∧ Cont P C T ∧ Cont S R T)
        (fun row : BHist =>
          hsame row N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro obligations
  obtain ⟨hK, hP, hC, hS, hW, hR, hH, hT, hQ, hN, hKW, hPC, hSR, hQpkg,
    hNpkg⟩ := obligations
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N
          ⟨hsame_refl N, hK, hP, hC, hS, hW, hR, hH, hT, hQ, hN, hKW, hPC,
            hSR, hQpkg, hNpkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      obtain ⟨same, _hK, _hP, _hC, _hS, _hW, _hR, _hH, _hT, _hQ, _hN, hKW,
        hPC, hSR, _hQpkg, _hNpkg⟩ := source
      exact ⟨same, hKW, hPC, hSR⟩
    ledger_sound := by
      intro _row source
      obtain ⟨same, _hK, _hP, _hC, _hS, _hW, _hR, _hH, _hT, _hQ, _hN, _hKW,
        _hPC, _hSR, hQpkg, hNpkg⟩ := source
      exact ⟨same, hQpkg, hNpkg⟩
  }

end BEDC.Derived.CompactPolishSpaceUp

namespace BEDC.Derived.CompactPolishSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactPolishSpaceUp : Type where
  | mk (K P C S W R H T Q N : BHist) : CompactPolishSpaceUp
  deriving DecidableEq

def compactPolishSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactPolishSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactPolishSpaceEncodeBHist h

def compactPolishSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactPolishSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactPolishSpaceDecodeBHist tail)

theorem CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactPolishSpaceFields : CompactPolishSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactPolishSpaceUp.mk K P C S W R H T Q N => [K, P, C, S, W, R, H, T, Q, N]

def compactPolishSpaceToEventFlow : CompactPolishSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactPolishSpaceFields x).map compactPolishSpaceEncodeBHist

def compactPolishSpaceFromEventFlow : EventFlow → Option CompactPolishSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _K :: [] => none
  | _K :: _P :: [] => none
  | _K :: _P :: _C :: [] => none
  | _K :: _P :: _C :: _S :: [] => none
  | _K :: _P :: _C :: _S :: _W :: [] => none
  | _K :: _P :: _C :: _S :: _W :: _R :: [] => none
  | _K :: _P :: _C :: _S :: _W :: _R :: _H :: [] => none
  | _K :: _P :: _C :: _S :: _W :: _R :: _H :: _T :: [] => none
  | _K :: _P :: _C :: _S :: _W :: _R :: _H :: _T :: _Q :: [] => none
  | K :: P :: C :: S :: W :: R :: H :: T :: Q :: N :: [] =>
      some
        (CompactPolishSpaceUp.mk
          (compactPolishSpaceDecodeBHist K)
          (compactPolishSpaceDecodeBHist P)
          (compactPolishSpaceDecodeBHist C)
          (compactPolishSpaceDecodeBHist S)
          (compactPolishSpaceDecodeBHist W)
          (compactPolishSpaceDecodeBHist R)
          (compactPolishSpaceDecodeBHist H)
          (compactPolishSpaceDecodeBHist T)
          (compactPolishSpaceDecodeBHist Q)
          (compactPolishSpaceDecodeBHist N))
  | _K :: _P :: _C :: _S :: _W :: _R :: _H :: _T :: _Q :: _N :: _extra :: _rest =>
      none

theorem CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactPolishSpaceUp,
      compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K P C S W R H T Q N =>
      change
        some
          (CompactPolishSpaceUp.mk
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist K))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist P))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist C))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist S))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist W))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist R))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist H))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist T))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist Q))
            (compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist N))) =
          some (CompactPolishSpaceUp.mk K P C S W R H T Q N)
      rw [CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode K,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode P,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode C,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode S,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode W,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode R,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode H,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode T,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode N]

theorem CompactPolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactPolishSpaceUp} :
    compactPolishSpaceToEventFlow x = compactPolishSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) =
        compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow y) :=
    congrArg compactPolishSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip y)))

theorem CompactPolishSpaceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CompactPolishSpaceUp,
      compactPolishSpaceFields x = compactPolishSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk K₁ P₁ C₁ S₁ W₁ R₁ H₁ T₁ Q₁ N₁ =>
      cases y with
      | mk K₂ P₂ C₂ S₂ W₂ R₂ H₂ T₂ Q₂ N₂ =>
          injection h with hK restP
          injection restP with hP restC
          injection restC with hC restS
          injection restS with hS restW
          injection restW with hW restR
          injection restR with hR restH
          injection restH with hH restT
          injection restT with hT restQ
          injection restQ with hQ restN
          injection restN with hN _
          subst hK
          subst hP
          subst hC
          subst hS
          subst hW
          subst hR
          subst hH
          subst hT
          subst hQ
          subst hN
          rfl

instance compactPolishSpaceBHistCarrier :
    BHistCarrier CompactPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactPolishSpaceToEventFlow
  fromEventFlow := compactPolishSpaceFromEventFlow

instance compactPolishSpaceChapterTasteGate :
    ChapterTasteGate CompactPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) = some x
    exact CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactPolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactPolishSpaceFieldFaithful :
    FieldFaithful CompactPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactPolishSpaceFields
  field_faithful := CompactPolishSpaceTasteGate_single_carrier_alignment_field_faithful

instance compactPolishSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactPolishSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactPolishSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactPolishSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def compactPolishSpaceTasteGate : ChapterTasteGate CompactPolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactPolishSpaceChapterTasteGate

def taste_gate : ChapterTasteGate CompactPolishSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactPolishSpaceChapterTasteGate

theorem CompactPolishSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactPolishSpaceUp) ∧
      Nonempty (FieldFaithful CompactPolishSpaceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactPolishSpaceUp) ∧
          (∀ h : BHist, compactPolishSpaceDecodeBHist (compactPolishSpaceEncodeBHist h) = h) ∧
            (∀ x : CompactPolishSpaceUp,
              compactPolishSpaceFromEventFlow (compactPolishSpaceToEventFlow x) = some x) ∧
              (∀ x y : CompactPolishSpaceUp,
                compactPolishSpaceToEventFlow x = compactPolishSpaceToEventFlow y → x = y) ∧
                compactPolishSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨compactPolishSpaceChapterTasteGate⟩
  · constructor
    · exact ⟨compactPolishSpaceFieldFaithful⟩
    · constructor
      · exact ⟨compactPolishSpaceNontrivial⟩
      · constructor
        · exact CompactPolishSpaceTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CompactPolishSpaceTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro _ _ heq
              exact CompactPolishSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.CompactPolishSpaceUp.TasteGate
