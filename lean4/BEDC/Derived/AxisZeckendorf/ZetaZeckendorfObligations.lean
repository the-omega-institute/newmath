import BEDC.Derived.AxisZeckendorf.GoldenPhaseProjection
import BEDC.Derived.RHRoute.FinitePrimeWindow

namespace BEDC.Derived.AxisZeckendorf.ZetaZeckendorfObligations

abbrev Bit : Type :=
  BEDC.Derived.AxisZeckendorf.GoldenPhaseProjection.Bit

abbrev NoAdjacentOne : List Bit -> Prop :=
  BEDC.Derived.AxisZeckendorf.GoldenPhaseProjection.NoAdjacentOne

abbrev PrimeWindow : Type :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev IsPrime : Nat -> Prop :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime

abbrev WindowAllPrime (W : PrimeWindow) : Prop :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.All IsPrime W.elems

structure ZetaToZeckendorfObligations where
  carrier : Type
  encodePrimeLocal : Nat -> carrier -> List Bit
  no11_encode :
    (p : Nat) -> IsPrime p -> (x : carrier) ->
      NoAdjacentOne (encodePrimeLocal p x)
  readback : List Bit -> carrier -> Nat
  finite_window_sound : PrimeWindow -> carrier -> Prop

namespace ZetaToZeckendorfObligations

def EncodedWord (O : ZetaToZeckendorfObligations) (p : Nat) (x : O.carrier) :
    List Bit :=
  O.encodePrimeLocal p x

def ReadbackValue (O : ZetaToZeckendorfObligations) (bits : List Bit) (x : O.carrier) :
    Nat :=
  O.readback bits x

def WindowSound (O : ZetaToZeckendorfObligations) (W : PrimeWindow) (x : O.carrier) :
    Prop :=
  O.finite_window_sound W x

theorem encoded_word_no11 (O : ZetaToZeckendorfObligations)
    (p : Nat) (hp : IsPrime p) (x : O.carrier) :
    NoAdjacentOne (O.EncodedWord p x) := by
  exact O.no11_encode p hp x

theorem readback_total (O : ZetaToZeckendorfObligations)
    (bits : List Bit) (x : O.carrier) :
    O.ReadbackValue bits x = O.readback bits x := by
  rfl

theorem window_sound_is_field (O : ZetaToZeckendorfObligations)
    (W : PrimeWindow) (x : O.carrier) :
    O.WindowSound W x = O.finite_window_sound W x := by
  rfl

end ZetaToZeckendorfObligations

def minimalEncodePrimeLocal (_p : Nat) (_x : Unit) : List Bit :=
  []

def minimalReadback (_bits : List Bit) (_x : Unit) : Nat :=
  0

def minimalFiniteWindowSound (W : PrimeWindow) (_x : Unit) : Prop :=
  WindowAllPrime W

theorem minimal_encode_no11 (p : Nat) (_hp : IsPrime p) (x : Unit) :
    NoAdjacentOne (minimalEncodePrimeLocal p x) := by
  exact BEDC.Derived.AxisZeckendorf.GoldenPhaseProjection.NoAdjacentOne.nil

theorem minimal_readback_total (bits : List Bit) (x : Unit) :
    minimalReadback bits x = 0 := by
  rfl

theorem minimal_window_sound (W : PrimeWindow) (x : Unit) :
    minimalFiniteWindowSound W x := by
  exact W.all_prime

def minimalZetaToZeckendorfObligations : ZetaToZeckendorfObligations where
  carrier := Unit
  encodePrimeLocal := minimalEncodePrimeLocal
  no11_encode := minimal_encode_no11
  readback := minimalReadback
  finite_window_sound := minimalFiniteWindowSound

theorem minimal_obligations_encode_no11
    (p : Nat) (hp : IsPrime p)
    (x : minimalZetaToZeckendorfObligations.carrier) :
    NoAdjacentOne (minimalZetaToZeckendorfObligations.encodePrimeLocal p x) := by
  exact minimalZetaToZeckendorfObligations.no11_encode p hp x

theorem minimal_obligations_readback_total
    (bits : List Bit) (x : minimalZetaToZeckendorfObligations.carrier) :
    minimalZetaToZeckendorfObligations.readback bits x = 0 := by
  rfl

theorem minimal_obligations_window_sound
    (W : PrimeWindow) (x : minimalZetaToZeckendorfObligations.carrier) :
    minimalZetaToZeckendorfObligations.finite_window_sound W x := by
  exact W.all_prime

end BEDC.Derived.AxisZeckendorf.ZetaZeckendorfObligations
