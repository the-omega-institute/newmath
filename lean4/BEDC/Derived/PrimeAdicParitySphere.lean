import BEDC.Derived.PadicValuationUp

namespace BEDC.Derived.PrimeAdicParitySphere

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicValuationUp

def parityEvenToken : BHist :=
  BHist.Empty

def parityOddToken : BHist :=
  BHist.e1 BHist.Empty

/-- 一元自然数上的闭生成宇称读数。 -/
inductive UnaryParity : BHist -> BHist -> Prop where
  | zero : UnaryParity BHist.Empty parityEvenToken
  | succ_even {n : BHist} :
      UnaryParity n parityEvenToken -> UnaryParity (BHist.e1 n) parityOddToken
  | succ_odd {n : BHist} :
      UnaryParity n parityOddToken -> UnaryParity (BHist.e1 n) parityEvenToken

theorem UnaryParity_input_unary {n parity : BHist} :
    UnaryParity n parity -> UnaryHistory n := by
  intro parityRead
  induction parityRead with
  | zero =>
      exact unary_empty
  | succ_even _ ih =>
      exact unary_e1_closed ih
  | succ_odd _ ih =>
      exact unary_e1_closed ih

theorem UnaryParity_token_cases {n parity : BHist} :
    UnaryParity n parity ->
      hsame parity parityEvenToken ∨ hsame parity parityOddToken := by
  intro parityRead
  induction parityRead with
  | zero =>
      exact Or.inl (hsame_refl parityEvenToken)
  | succ_even _ =>
      exact Or.inr (hsame_refl parityOddToken)
  | succ_odd _ =>
      exact Or.inl (hsame_refl parityEvenToken)

theorem UnaryParity_token_unary {n parity : BHist} :
    UnaryParity n parity -> UnaryHistory parity := by
  intro parityRead
  have tokenCases := UnaryParity_token_cases parityRead
  cases tokenCases with
  | inl evenToken =>
      cases evenToken
      exact unary_empty
  | inr oddToken =>
      cases oddToken
      exact unary_e1_closed unary_empty

theorem UnaryParity_unique {n left right : BHist} :
    UnaryParity n left -> UnaryParity n right -> hsame left right := by
  intro leftRead
  induction leftRead generalizing right with
  | zero =>
      intro rightRead
      cases rightRead
      exact hsame_refl parityEvenToken
  | succ_even previous ih =>
      intro rightRead
      cases rightRead with
      | succ_even rightPrevious =>
          exact hsame_refl parityOddToken
      | succ_odd rightPrevious =>
          have impossible : hsame parityEvenToken parityOddToken :=
            ih rightPrevious
          cases impossible
  | succ_odd previous ih =>
      intro rightRead
      cases rightRead with
      | succ_even rightPrevious =>
          have impossible : hsame parityOddToken parityEvenToken :=
            ih rightPrevious
          cases impossible
      | succ_odd rightPrevious =>
          exact hsame_refl parityEvenToken

theorem UnaryParity_total {n : BHist} :
    UnaryHistory n -> ∃ parity : BHist, UnaryParity n parity := by
  intro nUnary
  exact unary_history_induction
    (P := fun n => ∃ parity : BHist, UnaryParity n parity)
    (Exists.intro parityEvenToken UnaryParity.zero)
    (fun _n _nUnary previous =>
      match previous with
      | Exists.intro parity parityRead =>
          match UnaryParity_token_cases parityRead with
          | Or.inl evenToken =>
              by
                cases evenToken
                exact Exists.intro parityOddToken (UnaryParity.succ_even parityRead)
          | Or.inr oddToken =>
              by
                cases oddToken
                exact Exists.intro parityEvenToken (UnaryParity.succ_odd parityRead))
    n nUnary

def PadicSphereLayer (p radius x : BHist) : Prop :=
  NatPrime p ∧ padicValuationNat p x radius

def padicParitySphereInvariant (x parity : BHist) : Prop :=
  UnaryParity x parity

def PadicParitySphere (p radius x parity : BHist) : Prop :=
  PadicSphereLayer p radius x ∧ padicParitySphereInvariant x parity

theorem PadicSphereLayer_prime {p radius x : BHist} :
    PadicSphereLayer p radius x -> NatPrime p := by
  intro layer
  exact layer.left

theorem PadicSphereLayer_valuation {p radius x : BHist} :
    PadicSphereLayer p radius x -> padicValuationNat p x radius := by
  intro layer
  exact layer.right

theorem PadicParitySphere_layer {p radius x parity : BHist} :
    PadicParitySphere p radius x parity -> PadicSphereLayer p radius x := by
  intro sphere
  exact sphere.left

theorem PadicParitySphere_invariant {p radius x parity : BHist} :
    PadicParitySphere p radius x parity ->
      padicParitySphereInvariant x parity := by
  intro sphere
  exact sphere.right

theorem PadicParitySphere_input_unary {p radius x parity : BHist} :
    PadicParitySphere p radius x parity -> UnaryHistory x := by
  intro sphere
  exact UnaryParity_input_unary sphere.right

theorem PadicParitySphere_token_unary {p radius x parity : BHist} :
    PadicParitySphere p radius x parity -> UnaryHistory parity := by
  intro sphere
  exact UnaryParity_token_unary sphere.right

theorem PadicSphereLayer_radius_unique {p x leftRadius rightRadius : BHist} :
    PadicSphereLayer p leftRadius x -> PadicSphereLayer p rightRadius x ->
      hsame leftRadius rightRadius := by
  intro leftLayer rightLayer
  exact padicValuationNat_unique leftLayer.right rightLayer.right

theorem PadicParitySphere_radius_stratification
    {p x leftRadius rightRadius leftParity rightParity : BHist} :
    PadicParitySphere p leftRadius x leftParity ->
      PadicParitySphere p rightRadius x rightParity ->
        hsame leftRadius rightRadius := by
  intro leftSphere rightSphere
  exact PadicSphereLayer_radius_unique leftSphere.left rightSphere.left

theorem padicParitySphereInvariant_conserved
    {p radius x y leftParity rightParity : BHist} :
    PadicParitySphere p radius x leftParity ->
      PadicParitySphere p radius y rightParity ->
        hsame x y -> hsame leftParity rightParity := by
  intro leftSphere rightSphere samePoint
  cases samePoint
  exact UnaryParity_unique leftSphere.right rightSphere.right

theorem padicParitySphere_same_point_transport
    {p radius x y parity : BHist} :
    PadicParitySphere p radius x parity ->
      hsame x y -> padicValuationNat p y radius ->
        PadicParitySphere p radius y parity := by
  intro sphere samePoint valuationY
  cases samePoint
  exact ⟨⟨sphere.left.left, valuationY⟩, sphere.right⟩

theorem padicParitySphere_layered_conservation
    {p x y leftRadius rightRadius leftParity rightParity : BHist} :
    PadicParitySphere p leftRadius x leftParity ->
      PadicParitySphere p rightRadius y rightParity ->
        hsame x y ->
          hsame leftRadius rightRadius ∧ hsame leftParity rightParity := by
  intro leftSphere rightSphere samePoint
  cases samePoint
  exact
    ⟨PadicSphereLayer_radius_unique leftSphere.left rightSphere.left,
      UnaryParity_unique leftSphere.right rightSphere.right⟩

end BEDC.Derived.PrimeAdicParitySphere
