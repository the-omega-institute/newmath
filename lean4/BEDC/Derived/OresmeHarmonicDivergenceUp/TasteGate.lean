import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OresmeHarmonicDivergenceUp

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

inductive OresmeHarmonicDivergenceUp : Type where
  | mk (S B Q D W R E T C P N : BHist) : OresmeHarmonicDivergenceUp
  deriving DecidableEq

def oresmeHarmonicDivergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oresmeHarmonicDivergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oresmeHarmonicDivergenceEncodeBHist h

def oresmeHarmonicDivergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oresmeHarmonicDivergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oresmeHarmonicDivergenceDecodeBHist tail)

private theorem OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      oresmeHarmonicDivergenceDecodeBHist
          (oresmeHarmonicDivergenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oresmeHarmonicDivergenceToEventFlow : OresmeHarmonicDivergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OresmeHarmonicDivergenceUp.mk S B Q D W R E T C P N =>
      [oresmeHarmonicDivergenceEncodeBHist S,
        oresmeHarmonicDivergenceEncodeBHist B,
        oresmeHarmonicDivergenceEncodeBHist Q,
        oresmeHarmonicDivergenceEncodeBHist D,
        oresmeHarmonicDivergenceEncodeBHist W,
        oresmeHarmonicDivergenceEncodeBHist R,
        oresmeHarmonicDivergenceEncodeBHist E,
        oresmeHarmonicDivergenceEncodeBHist T,
        oresmeHarmonicDivergenceEncodeBHist C,
        oresmeHarmonicDivergenceEncodeBHist P,
        oresmeHarmonicDivergenceEncodeBHist N]

private def oresmeHarmonicDivergenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => oresmeHarmonicDivergenceEventAtDefault index rest

def oresmeHarmonicDivergenceFromEventFlow
    (ef : EventFlow) : Option OresmeHarmonicDivergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OresmeHarmonicDivergenceUp.mk
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 0 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 1 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 2 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 3 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 4 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 5 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 6 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 7 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 8 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 9 ef))
      (oresmeHarmonicDivergenceDecodeBHist
        (oresmeHarmonicDivergenceEventAtDefault 10 ef)))

private theorem OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OresmeHarmonicDivergenceUp,
      oresmeHarmonicDivergenceFromEventFlow
          (oresmeHarmonicDivergenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S B Q D W R E T C P N =>
      change
        some
            (OresmeHarmonicDivergenceUp.mk
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist S))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist B))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist Q))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist D))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist W))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist R))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist E))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist T))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist C))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist P))
              (oresmeHarmonicDivergenceDecodeBHist
                (oresmeHarmonicDivergenceEncodeBHist N))) =
          some (OresmeHarmonicDivergenceUp.mk S B Q D W R E T C P N)
      rw [OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode S,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode B,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode Q,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode D,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode W,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode R,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode E,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode T,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode C,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode P,
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode N]

private theorem
    OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OresmeHarmonicDivergenceUp} :
    oresmeHarmonicDivergenceToEventFlow x = oresmeHarmonicDivergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oresmeHarmonicDivergenceFromEventFlow (oresmeHarmonicDivergenceToEventFlow x) =
        oresmeHarmonicDivergenceFromEventFlow
          (oresmeHarmonicDivergenceToEventFlow y) :=
    congrArg oresmeHarmonicDivergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip y)))

instance oresmeHarmonicDivergenceBHistCarrier :
    BHistCarrier OresmeHarmonicDivergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oresmeHarmonicDivergenceToEventFlow
  fromEventFlow := oresmeHarmonicDivergenceFromEventFlow

instance oresmeHarmonicDivergenceChapterTasteGate :
    ChapterTasteGate OresmeHarmonicDivergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      oresmeHarmonicDivergenceFromEventFlow
          (oresmeHarmonicDivergenceToEventFlow x) =
        some x
    exact OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate OresmeHarmonicDivergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oresmeHarmonicDivergenceChapterTasteGate

theorem OresmeHarmonicDivergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        oresmeHarmonicDivergenceDecodeBHist
            (oresmeHarmonicDivergenceEncodeBHist h) =
          h) ∧
      (∀ x : OresmeHarmonicDivergenceUp,
        oresmeHarmonicDivergenceFromEventFlow
            (oresmeHarmonicDivergenceToEventFlow x) =
          some x) ∧
        (∀ x y : OresmeHarmonicDivergenceUp,
          oresmeHarmonicDivergenceToEventFlow x =
              oresmeHarmonicDivergenceToEventFlow y →
            x = y) ∧
          oresmeHarmonicDivergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_decode,
      OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        OresmeHarmonicDivergenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

theorem OresmeHarmonicDivergenceNameCertObligations [AskSetup] [PackageSetup]
    {S B Q D W R E T C P N blockRead comparisonRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory B →
        UnaryHistory Q →
          UnaryHistory D →
            UnaryHistory W →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory T →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont S B blockRead →
                          Cont Q D comparisonRead →
                            Cont W R sealRead →
                              Cont sealRead E namedRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row S ∨ hsame row B ∨ hsame row Q ∨
                                            hsame row D ∨ hsame row W ∨ hsame row R ∨
                                              hsame row E ∨ hsame row T ∨ hsame row C ∨
                                                hsame row P ∨ hsame row N ∨
                                                  hsame row blockRead ∨
                                                    hsame row comparisonRead ∨
                                                      hsame row sealRead ∨
                                                        hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont S B blockRead ∧
                                            Cont Q D comparisonRead ∧
                                              Cont W R sealRead ∧
                                                Cont sealRead E namedRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                        hsame ∧ UnaryHistory blockRead ∧
                                      UnaryHistory comparisonRead ∧ UnaryHistory sealRead ∧
                                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro sUnary bUnary qUnary dUnary wUnary rUnary eUnary _tUnary _pUnary _nUnary
    blockRoute comparisonRoute sealRoute namedRoute provenancePkg namePkg
  have blockUnary : UnaryHistory blockRead :=
    unary_cont_closed sUnary bUnary blockRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed qUnary dUnary comparisonRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed wUnary rUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary eUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row Q ∨ hsame row D ∨
              hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row T ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row blockRead ∨
                  hsame row comparisonRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B blockRead ∧ Cont Q D comparisonRead ∧
              Cont W R sealRead ∧ Cont sealRead E namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, blockRoute, comparisonRoute, sealRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, blockUnary, comparisonUnary, sealUnary, namedUnary⟩

end BEDC.Derived.OresmeHarmonicDivergenceUp
