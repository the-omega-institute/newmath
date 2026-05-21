import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HomotopyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HomotopyUp : Type where
  | mk (source target deformation interval provenance endpointRead ledger endpoint : BHist) :
      HomotopyUp
  deriving DecidableEq

def homotopyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: homotopyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: homotopyEncodeBHist h

def homotopyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (homotopyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (homotopyDecodeBHist tail)

private theorem homotopy_decode_encode :
    ∀ h : BHist, homotopyDecodeBHist (homotopyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def homotopyToEventFlow : HomotopyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | HomotopyUp.mk source target deformation interval provenance endpointRead ledger endpoint =>
      [homotopyEncodeBHist source,
        homotopyEncodeBHist target,
        homotopyEncodeBHist deformation,
        homotopyEncodeBHist interval,
        homotopyEncodeBHist provenance,
        homotopyEncodeBHist endpointRead,
        homotopyEncodeBHist ledger,
        homotopyEncodeBHist endpoint]

def homotopyFromEventFlow : EventFlow → Option HomotopyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | target :: rest1 =>
          match rest1 with
          | [] => none
          | deformation :: rest2 =>
              match rest2 with
              | [] => none
              | interval :: rest3 =>
                  match rest3 with
                  | [] => none
                  | provenance :: rest4 =>
                      match rest4 with
                      | [] => none
                      | endpointRead :: rest5 =>
                          match rest5 with
                          | [] => none
                          | ledger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | endpoint :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (HomotopyUp.mk
                                          (homotopyDecodeBHist source)
                                          (homotopyDecodeBHist target)
                                          (homotopyDecodeBHist deformation)
                                          (homotopyDecodeBHist interval)
                                          (homotopyDecodeBHist provenance)
                                          (homotopyDecodeBHist endpointRead)
                                          (homotopyDecodeBHist ledger)
                                          (homotopyDecodeBHist endpoint))
                                  | _ :: _ => none

private theorem homotopy_round_trip :
    ∀ x : HomotopyUp, homotopyFromEventFlow (homotopyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target deformation interval provenance endpointRead ledger endpoint =>
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (HomotopyUp.mk z
                  (homotopyDecodeBHist (homotopyEncodeBHist target))
                  (homotopyDecodeBHist (homotopyEncodeBHist deformation))
                  (homotopyDecodeBHist (homotopyEncodeBHist interval))
                  (homotopyDecodeBHist (homotopyEncodeBHist provenance))
                  (homotopyDecodeBHist (homotopyEncodeBHist endpointRead))
                  (homotopyDecodeBHist (homotopyEncodeBHist ledger))
                  (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
            (homotopy_decode_encode source))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (HomotopyUp.mk source z
                    (homotopyDecodeBHist (homotopyEncodeBHist deformation))
                    (homotopyDecodeBHist (homotopyEncodeBHist interval))
                    (homotopyDecodeBHist (homotopyEncodeBHist provenance))
                    (homotopyDecodeBHist (homotopyEncodeBHist endpointRead))
                    (homotopyDecodeBHist (homotopyEncodeBHist ledger))
                    (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
              (homotopy_decode_encode target))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (HomotopyUp.mk source target z
                      (homotopyDecodeBHist (homotopyEncodeBHist interval))
                      (homotopyDecodeBHist (homotopyEncodeBHist provenance))
                      (homotopyDecodeBHist (homotopyEncodeBHist endpointRead))
                      (homotopyDecodeBHist (homotopyEncodeBHist ledger))
                      (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
                (homotopy_decode_encode deformation))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (HomotopyUp.mk source target deformation z
                        (homotopyDecodeBHist (homotopyEncodeBHist provenance))
                        (homotopyDecodeBHist (homotopyEncodeBHist endpointRead))
                        (homotopyDecodeBHist (homotopyEncodeBHist ledger))
                        (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
                  (homotopy_decode_encode interval))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (HomotopyUp.mk source target deformation interval z
                          (homotopyDecodeBHist (homotopyEncodeBHist endpointRead))
                          (homotopyDecodeBHist (homotopyEncodeBHist ledger))
                          (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
                    (homotopy_decode_encode provenance))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (HomotopyUp.mk source target deformation interval provenance z
                            (homotopyDecodeBHist (homotopyEncodeBHist ledger))
                            (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
                      (homotopy_decode_encode endpointRead))
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          some
                            (HomotopyUp.mk source target deformation interval provenance
                              endpointRead z
                              (homotopyDecodeBHist (homotopyEncodeBHist endpoint))))
                        (homotopy_decode_encode ledger))
                      (congrArg
                        (fun z =>
                          some
                            (HomotopyUp.mk source target deformation interval provenance
                              endpointRead ledger z))
                        (homotopy_decode_encode endpoint))))))))

private theorem homotopyToEventFlow_injective {x y : HomotopyUp} :
    homotopyToEventFlow x = homotopyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      homotopyFromEventFlow (homotopyToEventFlow x) =
        homotopyFromEventFlow (homotopyToEventFlow y) :=
    congrArg homotopyFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (homotopy_round_trip x).symm (Eq.trans hread (homotopy_round_trip y))
  cases hsome
  rfl

instance homotopyBHistCarrier : BHistCarrier HomotopyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := homotopyToEventFlow
  fromEventFlow := homotopyFromEventFlow

instance homotopyChapterTasteGate : ChapterTasteGate HomotopyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change homotopyFromEventFlow (homotopyToEventFlow x) = some x
    exact homotopy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (homotopyToEventFlow_injective heq)

theorem HomotopyTasteGate_single_carrier_alignment :
    (∀ h : BHist, homotopyDecodeBHist (homotopyEncodeBHist h) = h) ∧
      (∀ x : HomotopyUp, homotopyFromEventFlow (homotopyToEventFlow x) = some x) ∧
        (∀ x y : HomotopyUp, homotopyToEventFlow x = homotopyToEventFlow y → x = y) ∧
      homotopyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨homotopy_decode_encode, homotopy_round_trip,
      fun x y heq => homotopyToEventFlow_injective heq, rfl⟩

end BEDC.Derived.HomotopyUp
