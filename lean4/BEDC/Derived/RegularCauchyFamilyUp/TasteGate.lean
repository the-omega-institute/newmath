import BEDC.Derived.RegularCauchyFamilyUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate
open BEDC.GroundCompiler.EventFlow

inductive RegularCauchyFamilyUp : Type where
  | mk :
      (memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
        provenance localCert : BHist) →
      RegularCauchyFamilyUp
  deriving DecidableEq

def regularCauchyFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFamilyEncodeBHist h

def regularCauchyFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFamilyDecodeBHist tail)

private theorem regularCauchyFamilyDecodeEncodeBHist :
    ∀ h : BHist, regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyFamilyFields : RegularCauchyFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFamilyUp.mk memberLedger memberRows modulus windows dyadicLedger
      diagonalRoute transports contRoutes provenance localCert =>
      [memberLedger, memberRows, modulus, windows, dyadicLedger, diagonalRoute, transports,
        contRoutes, provenance, localCert]

def regularCauchyFamilyToEventFlow : RegularCauchyFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyFamilyFields x).map regularCauchyFamilyEncodeBHist

def regularCauchyFamilyFromEventFlow : EventFlow → Option RegularCauchyFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | memberLedger :: rest0 =>
      match rest0 with
      | [] => none
      | memberRows :: rest1 =>
          match rest1 with
          | [] => none
          | modulus :: rest2 =>
              match rest2 with
              | [] => none
              | windows :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diagonalRoute :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transports :: rest6 =>
                              match rest6 with
                              | [] => none
                              | contRoutes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RegularCauchyFamilyUp.mk
                                                  (regularCauchyFamilyDecodeBHist memberLedger)
                                                  (regularCauchyFamilyDecodeBHist memberRows)
                                                  (regularCauchyFamilyDecodeBHist modulus)
                                                  (regularCauchyFamilyDecodeBHist windows)
                                                  (regularCauchyFamilyDecodeBHist dyadicLedger)
                                                  (regularCauchyFamilyDecodeBHist diagonalRoute)
                                                  (regularCauchyFamilyDecodeBHist transports)
                                                  (regularCauchyFamilyDecodeBHist contRoutes)
                                                  (regularCauchyFamilyDecodeBHist provenance)
                                                  (regularCauchyFamilyDecodeBHist localCert))
                                          | _ :: _ => none

private theorem regularCauchyFamily_round_trip :
    ∀ x : RegularCauchyFamilyUp,
      regularCauchyFamilyFromEventFlow (regularCauchyFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports
      contRoutes provenance localCert =>
      change
        some
          (RegularCauchyFamilyUp.mk
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist memberLedger))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist memberRows))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist modulus))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist windows))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist dyadicLedger))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist diagonalRoute))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist transports))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist contRoutes))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist provenance))
            (regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist localCert))) =
          some
            (RegularCauchyFamilyUp.mk memberLedger memberRows modulus windows dyadicLedger
              diagonalRoute transports contRoutes provenance localCert)
      rw [regularCauchyFamilyDecodeEncodeBHist memberLedger,
        regularCauchyFamilyDecodeEncodeBHist memberRows,
        regularCauchyFamilyDecodeEncodeBHist modulus,
        regularCauchyFamilyDecodeEncodeBHist windows,
        regularCauchyFamilyDecodeEncodeBHist dyadicLedger,
        regularCauchyFamilyDecodeEncodeBHist diagonalRoute,
        regularCauchyFamilyDecodeEncodeBHist transports,
        regularCauchyFamilyDecodeEncodeBHist contRoutes,
        regularCauchyFamilyDecodeEncodeBHist provenance,
        regularCauchyFamilyDecodeEncodeBHist localCert]

private theorem regularCauchyFamilyToEventFlow_injective {x y : RegularCauchyFamilyUp} :
    regularCauchyFamilyToEventFlow x = regularCauchyFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFamilyFromEventFlow (regularCauchyFamilyToEventFlow x) =
        regularCauchyFamilyFromEventFlow (regularCauchyFamilyToEventFlow y) :=
    congrArg regularCauchyFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyFamily_round_trip x).symm
      (Eq.trans hread (regularCauchyFamily_round_trip y)))

instance regularCauchyFamilyBHistCarrier : BHistCarrier RegularCauchyFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFamilyToEventFlow
  fromEventFlow := regularCauchyFamilyFromEventFlow

instance regularCauchyFamilyChapterTasteGate : ChapterTasteGate RegularCauchyFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFamilyFromEventFlow (regularCauchyFamilyToEventFlow x) = some x
    exact regularCauchyFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyFamilyToEventFlow_injective heq)

def RegularCauchyFamilyClassifier [AskSetup] [PackageSetup]
    (F F' : RegularCauchyFamilyUp) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame AskSetup PackageSetup
  match F, F' with
  | RegularCauchyFamilyUp.mk memberLedger memberRows modulus windows dyadicLedger
      diagonalRoute transports contRoutes provenance localCert,
    RegularCauchyFamilyUp.mk memberLedger' memberRows' modulus' windows' dyadicLedger'
      diagonalRoute' transports' contRoutes' provenance' localCert' =>
      hsame memberLedger memberLedger' ∧ hsame memberRows memberRows' ∧
        hsame modulus modulus' ∧ hsame windows windows' ∧
          hsame dyadicLedger dyadicLedger' ∧ hsame diagonalRoute diagonalRoute' ∧
            hsame transports transports' ∧ hsame contRoutes contRoutes' ∧
              hsame provenance provenance' ∧ hsame localCert localCert'

theorem RegularCauchyFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyFamilyDecodeBHist (regularCauchyFamilyEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyFamilyUp,
        regularCauchyFamilyFromEventFlow (regularCauchyFamilyToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyFamilyUp,
          regularCauchyFamilyToEventFlow x = regularCauchyFamilyToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyFamilyDecodeEncodeBHist
  · constructor
    · exact regularCauchyFamily_round_trip
    · intro x y heq
      exact regularCauchyFamilyToEventFlow_injective heq

end BEDC.Derived.RegularCauchyFamilyUp
