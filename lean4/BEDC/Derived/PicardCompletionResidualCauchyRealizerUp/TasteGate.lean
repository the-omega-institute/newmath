import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardCompletionResidualCauchyRealizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardCompletionResidualCauchyRealizerUp : Type where
  | mk
      (completeMetric contractionPicard finiteIterate residualDistance cauchyModulus
        completionHandoff regularReadback realSeal componentTransport replay provenance
        localName : BHist) :
      PicardCompletionResidualCauchyRealizerUp
  deriving DecidableEq

def picardCompletionResidualCauchyRealizerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardCompletionResidualCauchyRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardCompletionResidualCauchyRealizerEncodeBHist h

def picardCompletionResidualCauchyRealizerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardCompletionResidualCauchyRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardCompletionResidualCauchyRealizerDecodeBHist tail)

private theorem PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardCompletionResidualCauchyRealizerFields :
    PicardCompletionResidualCauchyRealizerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardCompletionResidualCauchyRealizerUp.mk completeMetric contractionPicard finiteIterate
      residualDistance cauchyModulus completionHandoff regularReadback realSeal
      componentTransport replay provenance localName =>
      [completeMetric, contractionPicard, finiteIterate, residualDistance, cauchyModulus,
        completionHandoff, regularReadback, realSeal, componentTransport, replay, provenance,
        localName]

def picardCompletionResidualCauchyRealizerToEventFlow :
    PicardCompletionResidualCauchyRealizerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (picardCompletionResidualCauchyRealizerFields x).map
        picardCompletionResidualCauchyRealizerEncodeBHist

private def picardCompletionResidualCauchyRealizerEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      picardCompletionResidualCauchyRealizerEventAtDefault index rest

def picardCompletionResidualCauchyRealizerFromEventFlow
    (ef : EventFlow) : Option PicardCompletionResidualCauchyRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PicardCompletionResidualCauchyRealizerUp.mk
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 0 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 1 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 2 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 3 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 4 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 5 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 6 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 7 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 8 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 9 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 10 ef))
      (picardCompletionResidualCauchyRealizerDecodeBHist
        (picardCompletionResidualCauchyRealizerEventAtDefault 11 ef)))

private theorem PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_round_trip :
    forall x : PicardCompletionResidualCauchyRealizerUp,
      picardCompletionResidualCauchyRealizerFromEventFlow
        (picardCompletionResidualCauchyRealizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk completeMetric contractionPicard finiteIterate residualDistance cauchyModulus
      completionHandoff regularReadback realSeal componentTransport replay provenance localName =>
      change
        some
          (PicardCompletionResidualCauchyRealizerUp.mk
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist completeMetric))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist contractionPicard))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist finiteIterate))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist residualDistance))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist cauchyModulus))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist completionHandoff))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist regularReadback))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist realSeal))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist componentTransport))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist replay))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist provenance))
            (picardCompletionResidualCauchyRealizerDecodeBHist
              (picardCompletionResidualCauchyRealizerEncodeBHist localName))) =
          some
            (PicardCompletionResidualCauchyRealizerUp.mk completeMetric contractionPicard
              finiteIterate residualDistance cauchyModulus completionHandoff regularReadback
              realSeal componentTransport replay provenance localName)
      rw [
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          completeMetric,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          contractionPicard,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          finiteIterate,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          residualDistance,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          cauchyModulus,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          completionHandoff,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          regularReadback,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          realSeal,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          componentTransport,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode replay,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
          provenance,
        PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode localName]

private theorem PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PicardCompletionResidualCauchyRealizerUp} :
    picardCompletionResidualCauchyRealizerToEventFlow x =
        picardCompletionResidualCauchyRealizerToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardCompletionResidualCauchyRealizerFromEventFlow
          (picardCompletionResidualCauchyRealizerToEventFlow x) =
        picardCompletionResidualCauchyRealizerFromEventFlow
          (picardCompletionResidualCauchyRealizerToEventFlow y) :=
    congrArg picardCompletionResidualCauchyRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_round_trip y)))

private theorem PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : PicardCompletionResidualCauchyRealizerUp,
      picardCompletionResidualCauchyRealizerFields x =
          picardCompletionResidualCauchyRealizerFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk completeMetric1 contractionPicard1 finiteIterate1 residualDistance1 cauchyModulus1
      completionHandoff1 regularReadback1 realSeal1 componentTransport1 replay1 provenance1
      localName1 =>
      cases y with
      | mk completeMetric2 contractionPicard2 finiteIterate2 residualDistance2 cauchyModulus2
          completionHandoff2 regularReadback2 realSeal2 componentTransport2 replay2 provenance2
          localName2 =>
          cases hfields
          rfl

instance picardCompletionResidualCauchyRealizerBHistCarrier :
    BHistCarrier PicardCompletionResidualCauchyRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardCompletionResidualCauchyRealizerToEventFlow
  fromEventFlow := picardCompletionResidualCauchyRealizerFromEventFlow

instance picardCompletionResidualCauchyRealizerChapterTasteGate :
    ChapterTasteGate PicardCompletionResidualCauchyRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance picardCompletionResidualCauchyRealizerFieldFaithful :
    FieldFaithful PicardCompletionResidualCauchyRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := picardCompletionResidualCauchyRealizerFields
  field_faithful :=
    PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_fields_faithful

instance picardCompletionResidualCauchyRealizerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PicardCompletionResidualCauchyRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PicardCompletionResidualCauchyRealizerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PicardCompletionResidualCauchyRealizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment :
    (forall h : BHist,
        picardCompletionResidualCauchyRealizerDecodeBHist
          (picardCompletionResidualCauchyRealizerEncodeBHist h) = h) ∧
      (forall x : PicardCompletionResidualCauchyRealizerUp,
        picardCompletionResidualCauchyRealizerFromEventFlow
          (picardCompletionResidualCauchyRealizerToEventFlow x) = some x) ∧
        (forall x y : PicardCompletionResidualCauchyRealizerUp,
          picardCompletionResidualCauchyRealizerToEventFlow x =
              picardCompletionResidualCauchyRealizerToEventFlow y ->
            x = y) ∧
          Nonempty (ChapterTasteGate PicardCompletionResidualCauchyRealizerUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          PicardCompletionResidualCauchyRealizerTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · exact ⟨picardCompletionResidualCauchyRealizerChapterTasteGate⟩

theorem PicardCompletionResidualCauchyRealizer_namecert_obligations
    [AskSetup] [PackageSetup] {X T I D M F R E H C Q N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X T D →
      Cont D M F →
        Cont F R E →
          PkgSig bundle Q pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row F ∨ hsame row R ∨ hsame row E)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row T ∨ hsame row I ∨ hsame row D ∨
                      hsame row M ∨ hsame row F ∨ hsame row R ∨ hsame row E ∨
                        hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N)
                  (fun _row : BHist =>
                    PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧ Cont X T D ∧
                      Cont D M F ∧ Cont F R E)
                  hsame ∧
                Cont X T D ∧ Cont D M F ∧ Cont F R E ∧ PkgSig bundle Q pkg ∧
                  PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro routeResidual routeCompletion routeReadback pkgProvenance namePkg
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row F ∨ hsame row R ∨ hsame row E)
          (fun row : BHist =>
            hsame row X ∨ hsame row T ∨ hsame row I ∨ hsame row D ∨
              hsame row M ∨ hsame row F ∨ hsame row R ∨ hsame row E ∨
                hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N)
          (fun _row : BHist =>
            PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧ Cont X T D ∧
              Cont D M F ∧ Cont F R E)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro F (Or.inl (hsame_refl F))
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
        have sameOtherRow : hsame _other _row := hsame_symm sameRows
        cases source with
        | inl sameF =>
            exact Or.inl (hsame_trans sameOtherRow sameF)
        | inr rest =>
            cases rest with
            | inl sameR =>
                exact Or.inr (Or.inl (hsame_trans sameOtherRow sameR))
            | inr sameE =>
                exact Or.inr (Or.inr (hsame_trans sameOtherRow sameE))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameF =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameF)))))
      | inr rest =>
          cases rest with
          | inl sameR =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl sameR))))))
          | inr sameE =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inl sameE)))))))
    ledger_sound := by
      intro _row _source
      exact ⟨pkgProvenance, namePkg, routeResidual, routeCompletion, routeReadback⟩
  }
  exact ⟨cert, routeResidual, routeCompletion, routeReadback, pkgProvenance, namePkg⟩

end BEDC.Derived.PicardCompletionResidualCauchyRealizerUp
