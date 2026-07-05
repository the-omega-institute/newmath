import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

/-!
# DimLiftBoundaryUp carrier.
-/

namespace BEDC.Derived.DimLiftBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite dimension-lift refusal boundary packet with the nine displayed BEDC rows. -/
inductive DimLiftBoundaryUp : Type where
  | mk :
      (carry normal cannotClaim fullAxis realRefusal transport route provenance name : BHist) →
      DimLiftBoundaryUp
  deriving DecidableEq

def dimLiftBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dimLiftBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dimLiftBoundaryEncodeBHist h

def dimLiftBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dimLiftBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dimLiftBoundaryDecodeBHist tail)

private theorem DimLiftBoundaryPacket_single_carrier_alignment_decode :
    ∀ h : BHist, dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dimLiftBoundaryToEventFlow : DimLiftBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route provenance
      name =>
      [[BMark.b0],
        dimLiftBoundaryEncodeBHist carry,
        [BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist normal,
        [BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist cannotClaim,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist fullAxis,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist realRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dimLiftBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dimLiftBoundaryEncodeBHist name]

def dimLiftBoundaryFromEventFlow : EventFlow → Option DimLiftBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | carry :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | normal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cannotClaim :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fullAxis :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realRefusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (DimLiftBoundaryUp.mk
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    carry)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    normal)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    cannotClaim)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    fullAxis)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    realRefusal)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    transport)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    route)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    provenance)
                                                                                  (dimLiftBoundaryDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem DimLiftBoundaryPacket_single_carrier_alignment_round :
    ∀ x : DimLiftBoundaryUp,
      dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carry normal cannotClaim fullAxis realRefusal transport route provenance name =>
      change
        some
          (DimLiftBoundaryUp.mk
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist carry))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
            (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name))) =
          some
            (DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
              provenance name)
      have hmk :
          DimLiftBoundaryUp.mk
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist carry))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) =
            DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
              provenance name := by
        calc
          DimLiftBoundaryUp.mk
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist carry))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
              (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) =
              DimLiftBoundaryUp.mk carry
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist normal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode carry)
          _ = DimLiftBoundaryUp.mk carry normal
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist cannotClaim))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode normal)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist fullAxis))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode cannotClaim)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist realRefusal))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode fullAxis)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist transport))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode realRefusal)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist route))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode transport)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                transport z
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist provenance))
                (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode route)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
                provenance (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)) :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                transport route z (dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist name)))
              (DimLiftBoundaryPacket_single_carrier_alignment_decode provenance)
          _ = DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal transport route
                provenance name :=
            congrArg
              (fun z => DimLiftBoundaryUp.mk carry normal cannotClaim fullAxis realRefusal
                transport route provenance z)
              (DimLiftBoundaryPacket_single_carrier_alignment_decode name)
      exact congrArg Option.some hmk

private theorem DimLiftBoundaryPacket_single_carrier_alignment_injective {x y : DimLiftBoundaryUp} :
    dimLiftBoundaryToEventFlow x = dimLiftBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) =
        dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow y) :=
    congrArg dimLiftBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DimLiftBoundaryPacket_single_carrier_alignment_round x).symm
      (Eq.trans hread (DimLiftBoundaryPacket_single_carrier_alignment_round y)))

instance dimLiftBoundaryBHistCarrier : BHistCarrier DimLiftBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dimLiftBoundaryToEventFlow
  fromEventFlow := dimLiftBoundaryFromEventFlow

instance dimLiftBoundaryChapterTasteGate : ChapterTasteGate DimLiftBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) = some x
    exact DimLiftBoundaryPacket_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DimLiftBoundaryPacket_single_carrier_alignment_injective heq)

theorem DimLiftBoundaryPacket_single_carrier_alignment :
    dimLiftBoundaryEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist, dimLiftBoundaryDecodeBHist (dimLiftBoundaryEncodeBHist h) = h) ∧
        (∀ x : DimLiftBoundaryUp,
          dimLiftBoundaryFromEventFlow (dimLiftBoundaryToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact DimLiftBoundaryPacket_single_carrier_alignment_decode
    · exact DimLiftBoundaryPacket_single_carrier_alignment_round

theorem DimLiftBoundaryCarrier_namecert_obligations {Z N A F R H C P Q : BHist} :
    SemanticNameCert
        (fun row : BHist => hsame row Q)
        (fun row : BHist =>
          hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨ hsame row R ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q)
        (fun row : BHist => hsame row row)
        hsame ∧
      Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist BMark NameCert SemanticNameCert
  constructor
  · constructor
    · constructor
      · exact ⟨Q, hsame_refl Q⟩
      · intro h _source
        exact hsame_refl h
      · intro h k same
        exact hsame_symm same
      · intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      · intro h k sameHK sourceH
        exact hsame_trans (hsame_symm sameHK) sourceH
    · intro h source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source)))))))
    · intro h _source
      exact hsame_refl h
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

theorem DimLiftBoundaryNonEscape {Z N A F R H C P Q consumerRead refusalRead : BHist} :
    Cont A R refusalRead →
      Cont C Q consumerRead →
        hsame consumerRead refusalRead →
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨ hsame row R ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q ∨
                    hsame row refusalRead ∨ hsame row consumerRead)
              (fun _row : BHist => Cont A R refusalRead ∧ Cont C Q consumerRead)
              hsame ∧
            Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro refusalRoute consumerRoute sameBoundary
  constructor
  · constructor
    · constructor
      · exact Exists.intro consumerRead (hsame_refl consumerRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      have _refusalSame : hsame _row refusalRead :=
        hsame_trans source sameBoundary
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inr source
    · intro _row _source
      exact ⟨refusalRoute, consumerRoute⟩
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

theorem DimLiftBoundaryPublicExport {Z N A F R H C P Q publicRead : BHist} :
    SemanticNameCert
        (fun row : BHist => hsame row publicRead)
        (fun row : BHist =>
          hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨ hsame row R ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q ∨
              hsame row publicRead)
        (fun row : BHist => hsame row row)
        hsame ∧
      Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert DimLiftBoundaryUp
  constructor
  · constructor
    · constructor
      · exact Exists.intro publicRead (hsame_refl publicRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source))))))))
    · intro row _source
      exact hsame_refl row
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

theorem DimLiftBoundaryAxisRefusalObligations
    {Z N A F R H C P Q axisRead refusalRead : BHist} :
    Cont Z N axisRead →
      Cont A R refusalRead →
        hsame axisRead refusalRead →
          SemanticNameCert
              (fun row : BHist => hsame row axisRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q ∨
                    hsame row refusalRead ∨ hsame row axisRead)
              (fun _row : BHist => Cont Z N axisRead ∧ Cont A R refusalRead)
              hsame ∧
            Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro axisRoute refusalRoute sameBoundary
  constructor
  · constructor
    · constructor
      · exact Exists.intro axisRead (hsame_refl axisRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      have _refusalSame : hsame _row refusalRead :=
        hsame_trans source sameBoundary
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source
    · intro _row _source
      exact ⟨axisRoute, refusalRoute⟩
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

theorem DimLiftBoundaryRealHandoffNonescape
    {Z N A F R H C P Q realRead refusalRead : BHist} :
    Cont R H realRead →
      Cont A R refusalRead →
        hsame realRead refusalRead →
          SemanticNameCert
              (fun row : BHist => hsame row realRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨ hsame row R ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row Q ∨
                    hsame row realRead ∨ hsame row refusalRead)
              (fun _row : BHist => Cont R H realRead ∧ Cont A R refusalRead)
              hsame ∧
            Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro realRoute refusalRoute sameBoundary
  constructor
  · constructor
    · constructor
      · exact Exists.intro realRead (hsame_refl realRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      have _refusalSame : hsame _row refusalRead :=
        hsame_trans source sameBoundary
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl source
    · intro _row _source
      exact ⟨realRoute, refusalRoute⟩
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

theorem DimLiftBoundaryZeckendorfCarrierScope
    {Z N A F R H C P Q scopeRead refusalRead : BHist} :
    Cont Z N scopeRead →
      Cont A R refusalRead →
        hsame scopeRead refusalRead →
          SemanticNameCert
              (fun row : BHist => hsame row scopeRead)
              (fun row : BHist =>
                hsame row Z ∨ hsame row N ∨ hsame row A ∨ hsame row F ∨
                  hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row Q ∨ hsame row scopeRead ∨ hsame row refusalRead)
              (fun _row : BHist => Cont Z N scopeRead ∧ Cont A R refusalRead)
              hsame ∧
            Nonempty DimLiftBoundaryUp := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert DimLiftBoundaryUp
  intro scopeRoute refusalRoute sameBoundary
  constructor
  · constructor
    · constructor
      · exact Exists.intro scopeRead (hsame_refl scopeRead)
      · intro row _source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    · intro _row source
      have _refusalSame : hsame _row refusalRead :=
        hsame_trans source sameBoundary
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl source
    · intro _row _source
      exact ⟨scopeRoute, refusalRoute⟩
  · exact Nonempty.intro (DimLiftBoundaryUp.mk Z N A F R H C P Q)

def DimLiftBoundaryClassifier (D1 D2 : DimLiftBoundaryUp) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame DimLiftBoundaryUp
  match D1, D2 with
  | DimLiftBoundaryUp.mk Z N A F R H C P Q, DimLiftBoundaryUp.mk Zp Np Ap Fp Rp Hp _Cp Pp Qp =>
      hsame Z Zp ∧ hsame N Np ∧ hsame A Ap ∧ hsame F Fp ∧ hsame R Rp ∧
        Cont H C Hp ∧ hsame P Pp ∧ hsame Q Qp ∧ Nonempty DimLiftBoundaryUp

end BEDC.Derived.DimLiftBoundaryUp
