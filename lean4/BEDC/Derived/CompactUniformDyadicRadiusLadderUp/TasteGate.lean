import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformDyadicRadiusLadderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformDyadicRadiusLadderUp : Type where
  | mk (X F G L D U H C P N : BHist) : CompactUniformDyadicRadiusLadderUp
  deriving DecidableEq

def compactUniformDyadicRadiusLadderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformDyadicRadiusLadderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformDyadicRadiusLadderEncodeBHist h

def compactUniformDyadicRadiusLadderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformDyadicRadiusLadderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformDyadicRadiusLadderDecodeBHist tail)

private theorem compactUniformDyadicRadiusLadder_decode_encode_bhist :
    ∀ h : BHist,
      compactUniformDyadicRadiusLadderDecodeBHist
        (compactUniformDyadicRadiusLadderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformDyadicRadiusLadderFields :
    CompactUniformDyadicRadiusLadderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformDyadicRadiusLadderUp.mk X F G L D U H C P N =>
      [X, F, G, L, D, U, H, C, P, N]

def compactUniformDyadicRadiusLadderToEventFlow :
    CompactUniformDyadicRadiusLadderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | carrier =>
      (compactUniformDyadicRadiusLadderFields carrier).map
        compactUniformDyadicRadiusLadderEncodeBHist

def compactUniformDyadicRadiusLadderFromEventFlow :
    EventFlow → Option CompactUniformDyadicRadiusLadderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [X, F, G, L, D, U, H, C, P, N] =>
      some
        (CompactUniformDyadicRadiusLadderUp.mk
          (compactUniformDyadicRadiusLadderDecodeBHist X)
          (compactUniformDyadicRadiusLadderDecodeBHist F)
          (compactUniformDyadicRadiusLadderDecodeBHist G)
          (compactUniformDyadicRadiusLadderDecodeBHist L)
          (compactUniformDyadicRadiusLadderDecodeBHist D)
          (compactUniformDyadicRadiusLadderDecodeBHist U)
          (compactUniformDyadicRadiusLadderDecodeBHist H)
          (compactUniformDyadicRadiusLadderDecodeBHist C)
          (compactUniformDyadicRadiusLadderDecodeBHist P)
          (compactUniformDyadicRadiusLadderDecodeBHist N))
  | _ => none

private theorem compactUniformDyadicRadiusLadder_round_trip :
    ∀ carrier : CompactUniformDyadicRadiusLadderUp,
      compactUniformDyadicRadiusLadderFromEventFlow
          (compactUniformDyadicRadiusLadderToEventFlow carrier) =
        some carrier := by
  -- BEDC touchpoint anchor: BHist BMark
  intro carrier
  cases carrier with
  | mk X F G L D U H C P N =>
      change
        some
          (CompactUniformDyadicRadiusLadderUp.mk
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist X))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist F))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist G))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist L))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist D))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist U))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist H))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist C))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist P))
            (compactUniformDyadicRadiusLadderDecodeBHist
              (compactUniformDyadicRadiusLadderEncodeBHist N))) =
          some (CompactUniformDyadicRadiusLadderUp.mk X F G L D U H C P N)
      rw [compactUniformDyadicRadiusLadder_decode_encode_bhist X,
        compactUniformDyadicRadiusLadder_decode_encode_bhist F,
        compactUniformDyadicRadiusLadder_decode_encode_bhist G,
        compactUniformDyadicRadiusLadder_decode_encode_bhist L,
        compactUniformDyadicRadiusLadder_decode_encode_bhist D,
        compactUniformDyadicRadiusLadder_decode_encode_bhist U,
        compactUniformDyadicRadiusLadder_decode_encode_bhist H,
        compactUniformDyadicRadiusLadder_decode_encode_bhist C,
        compactUniformDyadicRadiusLadder_decode_encode_bhist P,
        compactUniformDyadicRadiusLadder_decode_encode_bhist N]

private theorem compactUniformDyadicRadiusLadderToEventFlow_injective
    {x y : CompactUniformDyadicRadiusLadderUp} :
    compactUniformDyadicRadiusLadderToEventFlow x =
      compactUniformDyadicRadiusLadderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformDyadicRadiusLadderFromEventFlow
          (compactUniformDyadicRadiusLadderToEventFlow x) =
        compactUniformDyadicRadiusLadderFromEventFlow
          (compactUniformDyadicRadiusLadderToEventFlow y) :=
    congrArg compactUniformDyadicRadiusLadderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformDyadicRadiusLadder_round_trip x).symm
      (Eq.trans hread (compactUniformDyadicRadiusLadder_round_trip y)))

private theorem compactUniformDyadicRadiusLadder_field_faithful :
    ∀ x y : CompactUniformDyadicRadiusLadderUp,
      compactUniformDyadicRadiusLadderFields x =
        compactUniformDyadicRadiusLadderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ F₁ G₁ L₁ D₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ F₂ G₂ L₂ D₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactUniformDyadicRadiusLadderBHistCarrier :
    BHistCarrier CompactUniformDyadicRadiusLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformDyadicRadiusLadderToEventFlow
  fromEventFlow := compactUniformDyadicRadiusLadderFromEventFlow

instance compactUniformDyadicRadiusLadderChapterTasteGate :
    ChapterTasteGate CompactUniformDyadicRadiusLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformDyadicRadiusLadderFromEventFlow
        (compactUniformDyadicRadiusLadderToEventFlow x) = some x
    exact compactUniformDyadicRadiusLadder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformDyadicRadiusLadderToEventFlow_injective heq)

instance compactUniformDyadicRadiusLadderFieldFaithful :
    FieldFaithful CompactUniformDyadicRadiusLadderUp where
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  fields := compactUniformDyadicRadiusLadderFields
  field_faithful := compactUniformDyadicRadiusLadder_field_faithful

instance compactUniformDyadicRadiusLadderNontrivial :
    Nontrivial CompactUniformDyadicRadiusLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformDyadicRadiusLadderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformDyadicRadiusLadderUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactUniformDyadicRadiusLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformDyadicRadiusLadderChapterTasteGate

theorem CompactUniformDyadicRadiusLadderNameCertObligations [AskSetup] [PackageSetup]
    {X F G L D U H C P N centerRead radiusRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X F centerRead -> Cont G L radiusRead -> Cont D U uniformRead ->
      PkgSig bundle P pkg -> PkgSig bundle N pkg -> PkgSig bundle uniformRead pkg ->
        hsame H (append C P) ->
          SemanticNameCert
            (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
            (fun row : BHist =>
              hsame row uniformRead ∧ Cont X F centerRead ∧ Cont G L radiusRead ∧
                Cont D U uniformRead)
            (fun row : BHist =>
              hsame row uniformRead ∧ hsame H (append C P) ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg ∧ PkgSig bundle uniformRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro contXFCenter contGLRadius contDUUniform pkgP pkgN pkgUniform sameReplay
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact Exists.intro uniformRead (And.intro (hsame_refl uniformRead) pkgUniform)
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro row other sameRows source
    exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
  · intro _row source
    exact
      And.intro source.left
        (And.intro contXFCenter (And.intro contGLRadius contDUUniform))
  · intro _row source
    exact
      And.intro source.left
        (And.intro sameReplay (And.intro pkgP (And.intro pkgN source.right)))

end BEDC.Derived.CompactUniformDyadicRadiusLadderUp
