import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConceptRegistrySurfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConceptRegistrySurfaceUp : Type where
  | mk (C T G R S F U H P N : BHist) : ConceptRegistrySurfaceUp
  deriving DecidableEq

def conceptRegistrySurfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: conceptRegistrySurfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: conceptRegistrySurfaceEncodeBHist h

def conceptRegistrySurfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (conceptRegistrySurfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (conceptRegistrySurfaceDecodeBHist tail)

private def conceptRegistrySurfaceNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => conceptRegistrySurfaceNthRawEvent tail n

private theorem conceptRegistrySurface_decode_encode_bhist :
    ∀ h : BHist,
      conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem conceptRegistrySurface_mk_congr
    {C C' T T' G G' R R' S S' F F' U U' H H' P P' N N' : BHist}
    (hC : C' = C)
    (hT : T' = T)
    (hG : G' = G)
    (hR : R' = R)
    (hS : S' = S)
    (hF : F' = F)
    (hU : U' = U)
    (hH : H' = H)
    (hP : P' = P)
    (hN : N' = N) :
    ConceptRegistrySurfaceUp.mk C' T' G' R' S' F' U' H' P' N' =
      ConceptRegistrySurfaceUp.mk C T G R S F U H P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hC
  cases hT
  cases hG
  cases hR
  cases hS
  cases hF
  cases hU
  cases hH
  cases hP
  cases hN
  rfl

def conceptRegistrySurfaceFields : ConceptRegistrySurfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConceptRegistrySurfaceUp.mk C T G R S F U H P N => [C, T, G, R, S, F, U, H, P, N]

def conceptRegistrySurfaceToEventFlow : ConceptRegistrySurfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConceptRegistrySurfaceUp.mk C T G R S F U H P N =>
      [conceptRegistrySurfaceEncodeBHist C,
        conceptRegistrySurfaceEncodeBHist T,
        conceptRegistrySurfaceEncodeBHist G,
        conceptRegistrySurfaceEncodeBHist R,
        conceptRegistrySurfaceEncodeBHist S,
        conceptRegistrySurfaceEncodeBHist F,
        conceptRegistrySurfaceEncodeBHist U,
        conceptRegistrySurfaceEncodeBHist H,
        conceptRegistrySurfaceEncodeBHist P,
        conceptRegistrySurfaceEncodeBHist N]

def conceptRegistrySurfaceFromEventFlow (ef : EventFlow) : Option ConceptRegistrySurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConceptRegistrySurfaceUp.mk
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 0))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 1))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 2))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 3))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 4))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 5))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 6))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 7))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 8))
      (conceptRegistrySurfaceDecodeBHist (conceptRegistrySurfaceNthRawEvent ef 9)))

private theorem conceptRegistrySurface_round_trip :
    ∀ x : ConceptRegistrySurfaceUp,
      conceptRegistrySurfaceFromEventFlow (conceptRegistrySurfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C T G R S F U H P N =>
      exact
        congrArg some
          (conceptRegistrySurface_mk_congr
            (conceptRegistrySurface_decode_encode_bhist C)
            (conceptRegistrySurface_decode_encode_bhist T)
            (conceptRegistrySurface_decode_encode_bhist G)
            (conceptRegistrySurface_decode_encode_bhist R)
            (conceptRegistrySurface_decode_encode_bhist S)
            (conceptRegistrySurface_decode_encode_bhist F)
            (conceptRegistrySurface_decode_encode_bhist U)
            (conceptRegistrySurface_decode_encode_bhist H)
            (conceptRegistrySurface_decode_encode_bhist P)
            (conceptRegistrySurface_decode_encode_bhist N))

private theorem conceptRegistrySurfaceToEventFlow_injective
    {x y : ConceptRegistrySurfaceUp} :
    conceptRegistrySurfaceToEventFlow x = conceptRegistrySurfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      conceptRegistrySurfaceFromEventFlow (conceptRegistrySurfaceToEventFlow x) =
        conceptRegistrySurfaceFromEventFlow (conceptRegistrySurfaceToEventFlow y) :=
    congrArg conceptRegistrySurfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (conceptRegistrySurface_round_trip x).symm
      (Eq.trans hread (conceptRegistrySurface_round_trip y)))

private theorem conceptRegistrySurface_field_faithful :
    ∀ x y : ConceptRegistrySurfaceUp,
      conceptRegistrySurfaceFields x = conceptRegistrySurfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C T G R S F U H P N =>
      cases y with
      | mk C' T' G' R' S' F' U' H' P' N' =>
          cases hfields
          rfl

instance conceptRegistrySurfaceBHistCarrier : BHistCarrier ConceptRegistrySurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := conceptRegistrySurfaceToEventFlow
  fromEventFlow := conceptRegistrySurfaceFromEventFlow

instance conceptRegistrySurfaceChapterTasteGate :
    ChapterTasteGate ConceptRegistrySurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change conceptRegistrySurfaceFromEventFlow
      (conceptRegistrySurfaceToEventFlow x) = some x
    exact conceptRegistrySurface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (conceptRegistrySurfaceToEventFlow_injective heq)

instance conceptRegistrySurfaceFieldFaithful : FieldFaithful ConceptRegistrySurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := conceptRegistrySurfaceFields
  field_faithful := conceptRegistrySurface_field_faithful

instance conceptRegistrySurfaceNontrivial : Nontrivial ConceptRegistrySurfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConceptRegistrySurfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConceptRegistrySurfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConceptRegistrySurfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  conceptRegistrySurfaceChapterTasteGate

theorem ConceptRegistrySurfaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ConceptRegistrySurfaceUp) ∧
      Nonempty (FieldFaithful ConceptRegistrySurfaceUp) ∧
        Nonempty (Nontrivial ConceptRegistrySurfaceUp) ∧
          conceptRegistrySurfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨conceptRegistrySurfaceChapterTasteGate⟩,
      ⟨conceptRegistrySurfaceFieldFaithful⟩,
      ⟨conceptRegistrySurfaceNontrivial⟩,
      rfl⟩

def ConceptRegistrySurfaceCarrier [AskSetup] [PackageSetup]
    (C T G R S F U H P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  Cont C T G ∧ Cont G R S ∧ Cont S F U ∧ Cont U H P ∧ PkgSig bundle P pkg ∧
    PkgSig bundle N pkg

theorem ConceptRegistrySurface_forbidden_reading_refusal_certificate [AskSetup] [PackageSetup]
    {C T G R S F U H P N refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle F pkg ->
      PkgSig bundle N pkg ->
        hsame refusedRead F ->
          conceptRegistrySurfaceFields (ConceptRegistrySurfaceUp.mk C T G R S F U H P N) =
              [C, T, G, R, S, F, U, H, P, N] ∧
            SemanticNameCert
              (fun row : BHist => hsame row refusedRead ∨ hsame row F ∨ hsame row N)
              (fun row : BHist => hsame row refusedRead ∨ hsame row F ∨ hsame row N)
              (fun row : BHist =>
                (hsame row F ∧ PkgSig bundle F pkg) ∨
                  (hsame row N ∧ PkgSig bundle N pkg))
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro pkgF pkgN refusedSame
  have sourceRefused :
      (fun row : BHist => hsame row refusedRead ∨ hsame row F ∨ hsame row N)
        refusedRead := by
    exact Or.inl (hsame_refl refusedRead)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row refusedRead ∨ hsame row F ∨ hsame row N)
        (fun row : BHist => hsame row refusedRead ∨ hsame row F ∨ hsame row N)
        (fun row : BHist =>
          (hsame row F ∧ PkgSig bundle F pkg) ∨
            (hsame row N ∧ PkgSig bundle N pkg))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedRead sourceRefused
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
        cases source with
        | inl rowRefused =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowRefused)
        | inr tail =>
            cases tail with
            | inl rowF =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowF))
            | inr rowN =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowN))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      cases source with
      | inl rowRefused =>
          exact Or.inl ⟨hsame_trans rowRefused refusedSame, pkgF⟩
      | inr tail =>
          cases tail with
          | inl rowF =>
              exact Or.inl ⟨rowF, pkgF⟩
          | inr rowN =>
              exact Or.inr ⟨rowN, pkgN⟩
  }
  exact ⟨rfl, cert⟩

theorem ConceptRegistrySurface_export_exactness_certificate [AskSetup] [PackageSetup]
    {C T G R S F U H P N localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle P pkg →
      hsame localRead N →
        conceptRegistrySurfaceFields (ConceptRegistrySurfaceUp.mk C T G R S F U H P N) =
            [C, T, G, R, S, F, U, H, P, N] ∧
          SemanticNameCert
            (fun row : BHist => hsame row N)
            (fun row : BHist =>
              hsame row C ∨ hsame row T ∨ hsame row G ∨ hsame row R ∨ hsame row S ∨
                hsame row F ∨ hsame row U ∨ hsame row H ∨ hsame row P ∨ hsame row N)
            (fun row : BHist => hsame row localRead ∧ PkgSig bundle P pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro pkgP localReadSameName
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N)
        (fun row : BHist =>
          hsame row C ∨ hsame row T ∨ hsame row G ∨ hsame row R ∨ hsame row S ∨
            hsame row F ∨ hsame row U ∨ hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => hsame row localRead ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N (hsame_refl N)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))))
    ledger_sound := by
      intro _row source
      exact ⟨hsame_trans source (hsame_symm localReadSameName), pkgP⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.ConceptRegistrySurfaceUp
