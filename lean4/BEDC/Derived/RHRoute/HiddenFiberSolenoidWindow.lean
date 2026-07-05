namespace BEDC.Derived.RHRoute.HiddenFiberSolenoidWindow

abbrev Residue (_p _k : Nat) : Type :=
  Nat

def modulus (p k : Nat) : Nat :=
  p ^ (k + 1)

def reduceResidue (p k : Nat) (x : Residue p k) : Nat :=
  x % modulus p k

def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, Nat.succ _ => false
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natEqBool a b

theorem natEqBool_refl :
    (n : Nat) -> natEqBool n n = true
  | 0 => rfl
  | Nat.succ n => natEqBool_refl n

theorem natEqBool_true_eq :
    {a b : Nat} -> natEqBool a b = true -> a = b
  | 0, 0, _h => rfl
  | 0, Nat.succ _b, h => by
      cases h
  | Nat.succ _a, 0, h => by
      cases h
  | Nat.succ a, Nat.succ b, h => by
      exact congrArg Nat.succ (natEqBool_true_eq h)

theorem natEqBool_eq_true {a b : Nat} :
    a = b -> natEqBool a b = true := by
  intro h
  cases h
  exact natEqBool_refl a

theorem natEqBool_symm_true {a b : Nat} :
    natEqBool a b = true -> natEqBool b a = true := by
  intro h
  exact natEqBool_eq_true (Eq.symm (natEqBool_true_eq h))

theorem natEqBool_trans_true {a b c : Nat} :
    natEqBool a b = true ->
      natEqBool b c = true ->
        natEqBool a c = true := by
  intro left right
  exact natEqBool_eq_true
    (Eq.trans (natEqBool_true_eq left) (natEqBool_true_eq right))

def compatibleStep (p k : Nat) (lower upper : Nat) : Bool :=
  natEqBool (upper % modulus p k) (lower % modulus p k)

theorem compatibleStep_refl (p k x : Nat) :
    compatibleStep p k x x = true := by
  unfold compatibleStep
  exact natEqBool_refl (x % modulus p k)

theorem compatibleStep_sound {p k lower upper : Nat} :
    compatibleStep p k lower upper = true ->
      upper % modulus p k = lower % modulus p k := by
  unfold compatibleStep
  intro h
  exact natEqBool_true_eq h

theorem compatibleStep_of_same_residue {p k lower upper : Nat} :
    upper % modulus p k = lower % modulus p k ->
      compatibleStep p k lower upper = true := by
  intro h
  unfold compatibleStep
  exact natEqBool_eq_true h

theorem compatibleStep_trans {p k x y z : Nat} :
    compatibleStep p k x y = true ->
      compatibleStep p k y z = true ->
        compatibleStep p k x z = true := by
  intro left right
  exact compatibleStep_of_same_residue
    (Eq.trans (compatibleStep_sound right) (compatibleStep_sound left))

inductive CoherentChain (p : Nat) : Nat -> Nat -> Type where
  | base (x : Nat) : CoherentChain p 0 x
  | snoc {K last : Nat}
      (stem : CoherentChain p K last)
      (next : Nat)
      (compatible : compatibleStep p K last next = true) :
      CoherentChain p (Nat.succ K) next

structure CoherentWindow (p K : Nat) where
  top : Nat
  chain : CoherentChain p K top

namespace CoherentChain

def readFromTop {p K top : Nat}
    (chain : CoherentChain p K top) (depthFromTop : Nat) : Nat :=
  match chain, depthFromTop with
  | CoherentChain.base x, _depth => x
  | CoherentChain.snoc _stem next _compatible, 0 => next
  | CoherentChain.snoc stem _next _compatible, Nat.succ depth =>
      readFromTop stem depth

theorem readFromTop_zero {p K top : Nat}
    (chain : CoherentChain p K top) :
    readFromTop chain 0 = top := by
  cases chain with
  | base _x => rfl
  | snoc _stem _next _compatible => rfl

end CoherentChain

namespace CoherentWindow

def readFromTop {p K : Nat} (window : CoherentWindow p K)
    (depthFromTop : Nat) : Nat :=
  CoherentChain.readFromTop window.chain depthFromTop

theorem readFromTop_zero {p K : Nat}
    (window : CoherentWindow p K) :
    readFromTop window 0 = window.top := by
  exact CoherentChain.readFromTop_zero window.chain

def truncateTopCore {p K : Nat}
    (window : CoherentWindow p (Nat.succ K)) : CoherentWindow p K :=
  CoherentChain.casesOn
    (motive := fun depth _top _chain =>
      match depth with
      | 0 => Unit
      | Nat.succ pred => CoherentWindow p pred)
    window.chain
    (fun _x => ())
    (fun {_K} {last} stem _next _compatible =>
      { top := last, chain := stem })

def truncateTop {p K : Nat}
    (window : CoherentWindow p (Nat.succ K)) : CoherentWindow p K :=
  truncateTopCore window

theorem truncate_read_shift {p K : Nat}
    (window : CoherentWindow p (Nat.succ K))
    (depthFromTop : Nat) :
    readFromTop (truncateTop window) depthFromTop =
      readFromTop window (Nat.succ depthFromTop) :=
  CoherentChain.casesOn
    (motive := fun depth top chain =>
      match depth with
      | 0 => True
      | Nat.succ pred =>
          readFromTop
              (truncateTop
                ({ top := top, chain := chain } :
                  CoherentWindow p (Nat.succ pred)))
              depthFromTop =
            readFromTop
              ({ top := top, chain := chain } :
                CoherentWindow p (Nat.succ pred))
              (Nat.succ depthFromTop))
    window.chain
    (fun _x => True.intro)
    (fun {_K} {_last} stem next compatible =>
      Eq.refl
        (readFromTop
          (truncateTop
            { top := next,
              chain := CoherentChain.snoc stem next compatible })
          depthFromTop))

theorem truncate_top_compatible {p K : Nat}
    (window : CoherentWindow p (Nat.succ K)) :
    compatibleStep p K (truncateTop window).top window.top = true :=
  CoherentChain.casesOn
    (motive := fun depth top chain =>
      match depth with
      | 0 => True
      | Nat.succ pred =>
          compatibleStep p pred
              (truncateTop
                ({ top := top, chain := chain } :
                  CoherentWindow p (Nat.succ pred))).top
              ({ top := top, chain := chain } :
                CoherentWindow p (Nat.succ pred)).top =
            true)
    window.chain
    (fun _x => True.intro)
    (fun {_K} {_last} _stem _next compatible => compatible)

end CoherentWindow

def constantChain (p : Nat) :
    (K : Nat) -> (c : Nat) -> CoherentChain p K c
  | 0, c => CoherentChain.base c
  | Nat.succ K, c =>
      CoherentChain.snoc (constantChain p K c) c
        (compatibleStep_refl p K c)

def constantWindow (p K c : Nat) : CoherentWindow p K :=
  { top := c, chain := constantChain p K c }

theorem constantWindow_top (p K c : Nat) :
    (constantWindow p K c).top = c := by
  rfl

theorem constantChain_readFromTop_const (p : Nat) :
    (K c depthFromTop : Nat) ->
      CoherentChain.readFromTop (constantChain p K c) depthFromTop = c
  | 0, _c, _depthFromTop => rfl
  | Nat.succ _K, _c, 0 => rfl
  | Nat.succ K, c, Nat.succ depthFromTop =>
      constantChain_readFromTop_const p K c depthFromTop

theorem constantWindow_readFromTop_const
    (p K c depthFromTop : Nat) :
    CoherentWindow.readFromTop (constantWindow p K c) depthFromTop = c := by
  exact constantChain_readFromTop_const p K c depthFromTop

structure PrimeAxisWindow where
  prime : Nat
  depth : Nat
  top : Nat
  chain : CoherentChain prime depth top

namespace PrimeAxisWindow

def coherentWindow (axis : PrimeAxisWindow) :
    CoherentWindow axis.prime axis.depth :=
  { top := axis.top, chain := axis.chain }

def constant (p K c : Nat) : PrimeAxisWindow :=
  { prime := p, depth := K, top := c, chain := constantChain p K c }

theorem constant_top (p K c : Nat) :
    (constant p K c).top = c := by
  rfl

theorem constant_readFromTop (p K c depthFromTop : Nat) :
    CoherentWindow.readFromTop ((constant p K c).coherentWindow)
      depthFromTop = c := by
  exact constantWindow_readFromTop_const p K c depthFromTop

end PrimeAxisWindow

structure HiddenFiberProductWindow where
  axes : List PrimeAxisWindow

namespace HiddenFiberProductWindow

def empty : HiddenFiberProductWindow :=
  { axes := [] }

def axisCount (window : HiddenFiberProductWindow) : Nat :=
  window.axes.length

def extendAxis (window : HiddenFiberProductWindow)
    (axis : PrimeAxisWindow) : HiddenFiberProductWindow :=
  { axes := axis :: window.axes }

theorem empty_axisCount :
    axisCount empty = 0 := by
  rfl

theorem extendAxis_axisCount
    (window : HiddenFiberProductWindow)
    (axis : PrimeAxisWindow) :
    axisCount (extendAxis window axis) = Nat.succ (axisCount window) := by
  rfl

def constantSingleAxis (p K c : Nat) : HiddenFiberProductWindow :=
  extendAxis empty (PrimeAxisWindow.constant p K c)

theorem constantSingleAxis_axisCount (p K c : Nat) :
    axisCount (constantSingleAxis p K c) = 1 := by
  rfl

end HiddenFiberProductWindow

structure VisiblePhaseWindow where
  numerator : Nat
  denominator : Nat

namespace VisiblePhaseWindow

def zero : VisiblePhaseWindow :=
  { numerator := 0, denominator := 1 }

def samePhaseBool (left right : VisiblePhaseWindow) : Bool :=
  natEqBool left.numerator right.numerator

theorem samePhaseBool_refl (phase : VisiblePhaseWindow) :
    samePhaseBool phase phase = true := by
  unfold samePhaseBool
  exact natEqBool_refl phase.numerator

theorem zero_samePhaseBool :
    samePhaseBool zero zero = true := by
  rfl

end VisiblePhaseWindow

structure SolenoidWindow where
  visible : VisiblePhaseWindow
  hidden : HiddenFiberProductWindow

namespace SolenoidWindow

def projectVisible (window : SolenoidWindow) : VisiblePhaseWindow :=
  window.visible

def hiddenKernelWindow
    (hidden : HiddenFiberProductWindow) : SolenoidWindow :=
  { visible := VisiblePhaseWindow.zero, hidden := hidden }

def inVisibleKernelBool (window : SolenoidWindow) : Bool :=
  VisiblePhaseWindow.samePhaseBool window.visible VisiblePhaseWindow.zero

theorem hiddenKernelWindow_projects_zero
    (hidden : HiddenFiberProductWindow) :
    projectVisible (hiddenKernelWindow hidden) = VisiblePhaseWindow.zero := by
  rfl

theorem hiddenKernelWindow_inVisibleKernel
    (hidden : HiddenFiberProductWindow) :
    inVisibleKernelBool (hiddenKernelWindow hidden) = true := by
  rfl

theorem hiddenKernelWindow_hidden_exact
    (hidden : HiddenFiberProductWindow) :
    (hiddenKernelWindow hidden).hidden = hidden := by
  rfl

end SolenoidWindow

inductive HiddenFiberSolenoidCompletionObligationKind where
  | profiniteCharacterGroupQModZ
  | solenoidCharacterGroupQ
  | pontryaginExactSequence

structure HiddenFiberSolenoidCompletionObligation where
  kind : HiddenFiberSolenoidCompletionObligationKind
  finiteWindowAnchor : Nat

/--
needs propext-free completion, deferred: continuous-character and Pontryagin
duality statements require a finite-window-to-completion bridge.
-/
def profiniteCharacterDualObligation :
    HiddenFiberSolenoidCompletionObligation :=
  { kind :=
      HiddenFiberSolenoidCompletionObligationKind.profiniteCharacterGroupQModZ
    finiteWindowAnchor := 0 }

def solenoidCharacterDualObligation :
    HiddenFiberSolenoidCompletionObligation :=
  { kind := HiddenFiberSolenoidCompletionObligationKind.solenoidCharacterGroupQ
    finiteWindowAnchor := 0 }

def pontryaginExactSequenceObligation :
    HiddenFiberSolenoidCompletionObligation :=
  { kind := HiddenFiberSolenoidCompletionObligationKind.pontryaginExactSequence
    finiteWindowAnchor := 0 }

def hiddenFiberSolenoidCompletionObligations :
    List HiddenFiberSolenoidCompletionObligation :=
  [ profiniteCharacterDualObligation,
    solenoidCharacterDualObligation,
    pontryaginExactSequenceObligation ]

theorem hiddenFiberSolenoidCompletionObligation_count :
    hiddenFiberSolenoidCompletionObligations.length = 3 := by
  rfl

end BEDC.Derived.RHRoute.HiddenFiberSolenoidWindow
