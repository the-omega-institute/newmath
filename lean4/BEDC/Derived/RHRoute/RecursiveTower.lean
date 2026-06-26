import BEDC.Derived.RHRoute.FinitePrimeWindow

namespace BEDC.Derived.RHRoute.RecursiveTower

open BEDC.Derived.RHRoute.FinitePrimeWindow

universe u

inductive TraceEvent where
  | seed : Nat -> TraceEvent
  | refine : Nat -> Nat -> TraceEvent
  | readback : Nat -> Nat -> TraceEvent

structure CertifiedReturn (alpha : Type u) (P : alpha -> Prop) where
  value : alpha
  cert : P value
  trace : List TraceEvent

structure Layer where
  State : Type u
  window : PrimeWindow
  pred : State -> Prop

structure LayerStep (source target : Layer.{u}) where
  refine : source.State -> target.State
  readback : target.State -> source.State
  readback_refine : (s : source.State) -> readback (refine s) = s
  pred_refine : (s : source.State) -> source.pred s -> target.pred (refine s)
  pred_inherit : (t : target.State) -> target.pred t -> source.pred (readback t)

structure PrimeWindowTower where
  layer : Nat -> Layer.{u}
  seed : (layer 0).State
  seed_cert : (layer 0).pred seed
  step : (n : Nat) -> LayerStep (layer n) (layer (Nat.succ n))

def runTower (T : PrimeWindowTower.{u}) :
    (fuel : Nat) -> CertifiedReturn (T.layer fuel).State (T.layer fuel).pred
  | 0 => {
      value := T.seed
      cert := T.seed_cert
      trace := [TraceEvent.seed 0]
    }
  | Nat.succ n =>
      let previous := runTower T n
      let step := T.step n
      {
        value := step.refine previous.value
        cert := step.pred_refine previous.value previous.cert
        trace := previous.trace ++ [TraceEvent.refine n (Nat.succ n)]
      }

def readbackMany (T : PrimeWindowTower.{u}) :
    (fuel : Nat) -> (T.layer fuel).State -> (T.layer 0).State
  | 0, state => state
  | Nat.succ n, state => readbackMany T n ((T.step n).readback state)

def readbackTrace (fuel : Nat) : List TraceEvent :=
  match fuel with
  | 0 => []
  | Nat.succ n => TraceEvent.readback (Nat.succ n) n :: readbackTrace n

theorem readbackMany_pred_inherit (T : PrimeWindowTower.{u}) :
    (fuel : Nat) -> (state : (T.layer fuel).State) -> (T.layer fuel).pred state ->
      (T.layer 0).pred (readbackMany T fuel state)
  | 0, _state, stateCert => stateCert
  | Nat.succ n, state, stateCert =>
      readbackMany_pred_inherit T n ((T.step n).readback state)
        ((T.step n).pred_inherit state stateCert)

theorem runTower_readback_refine (T : PrimeWindowTower.{u}) :
    (fuel : Nat) -> readbackMany T fuel (runTower T fuel).value = T.seed
  | 0 => rfl
  | Nat.succ n => by
      change
        readbackMany T n
            ((T.step n).readback ((T.step n).refine (runTower T n).value)) =
          T.seed
      rw [(T.step n).readback_refine (runTower T n).value]
      exact runTower_readback_refine T n

theorem recursive_tower_readback_sound (T : PrimeWindowTower.{u}) (fuel : Nat) :
    (T.layer 0).pred (readbackMany T fuel (runTower T fuel).value) :=
  readbackMany_pred_inherit T fuel (runTower T fuel).value (runTower T fuel).cert

end BEDC.Derived.RHRoute.RecursiveTower
