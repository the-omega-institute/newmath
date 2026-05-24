import BEDC.Derived.NatUp

namespace BEDC.Derived.OrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

inductive OrderComparisonBranch (left right : BHist) : Type where
  | leftPrefix : NatUnaryStrictPrefix left right → OrderComparisonBranch left right
  | rightPrefix : NatUnaryStrictPrefix right left → OrderComparisonBranch left right
  | same : hsame left right → OrderComparisonBranch left right

structure OrderUnaryComparisonCarrier : Type where
  left : BHist
  right : BHist
  leftUnary : UnaryHistory left
  rightUnary : UnaryHistory right
  branch : OrderComparisonBranch left right

def OrderUnaryComparisonClassifier
    (Z W : OrderUnaryComparisonCarrier) : Prop :=
  hsame Z.left W.left ∧ hsame Z.right W.right

theorem OrderUnaryComparisonNameCertObligations :
    Nonempty OrderUnaryComparisonCarrier ∧
      (∀ Z : OrderUnaryComparisonCarrier, UnaryHistory Z.left ∧ UnaryHistory Z.right) ∧
        (∀ Z : OrderUnaryComparisonCarrier, OrderUnaryComparisonClassifier Z Z) ∧
          (∀ Z W : OrderUnaryComparisonCarrier,
            OrderUnaryComparisonClassifier Z W → OrderUnaryComparisonClassifier W Z) ∧
            (∀ Z W V : OrderUnaryComparisonCarrier,
              OrderUnaryComparisonClassifier Z W →
                OrderUnaryComparisonClassifier W V →
                  OrderUnaryComparisonClassifier Z V) := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory NatUnaryStrictPrefix
  constructor
  · exact
      ⟨OrderUnaryComparisonCarrier.mk BHist.Empty BHist.Empty unary_empty unary_empty
        (OrderComparisonBranch.same (hsame_refl BHist.Empty))⟩
  · constructor
    · intro Z
      exact ⟨Z.leftUnary, Z.rightUnary⟩
    · constructor
      · intro Z
        exact ⟨hsame_refl Z.left, hsame_refl Z.right⟩
      · constructor
        · intro Z W hZW
          exact ⟨hsame_symm hZW.left, hsame_symm hZW.right⟩
        · intro Z W V hZW hWV
          exact ⟨hsame_trans hZW.left hWV.left, hsame_trans hZW.right hWV.right⟩

theorem OrderUnaryComparison_obligation_prefix_ledger_exhaustion
    (Z : OrderUnaryComparisonCarrier) :
    UnaryHistory Z.left ∧ UnaryHistory Z.right ∧ OrderUnaryComparisonClassifier Z Z ∧
      (NatUnaryStrictPrefix Z.left Z.right ∨
        NatUnaryStrictPrefix Z.right Z.left ∨ hsame Z.left Z.right) := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory NatUnaryStrictPrefix
  obtain ⟨_inhabited, unaryRows, reflexiveClassifier, _symmetricClassifier,
    _transitiveClassifier⟩ := OrderUnaryComparisonNameCertObligations
  constructor
  · exact (unaryRows Z).left
  · constructor
    · exact (unaryRows Z).right
    · constructor
      · exact reflexiveClassifier Z
      · cases Z.branch with
        | leftPrefix leftStrict =>
            exact Or.inl leftStrict
        | rightPrefix rightStrict =>
            exact Or.inr (Or.inl rightStrict)
        | same sameEndpoints =>
            exact Or.inr (Or.inr sameEndpoints)

theorem OrderFullNatArithmeticHandoff :
    (∀ Z : OrderUnaryComparisonCarrier,
      UnaryHistory Z.left ∧
        UnaryHistory Z.right ∧
          (NatUnaryStrictPrefix Z.left Z.right ∨
            NatUnaryStrictPrefix Z.right Z.left ∨ hsame Z.left Z.right)) ∧
      (∀ {h k : BHist}, UnaryHistory h → UnaryHistory k →
        ∃ Z : OrderUnaryComparisonCarrier, Z.left = h ∧ Z.right = k) := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory NatUnaryStrictPrefix
  constructor
  · intro Z
    constructor
    · exact Z.leftUnary
    · constructor
      · exact Z.rightUnary
      · cases Z.branch with
        | leftPrefix hleft =>
            exact Or.inl hleft
        | rightPrefix hright =>
            exact Or.inr (Or.inl hright)
        | same hsameBranch =>
            exact Or.inr (Or.inr hsameBranch)
  · intro h k unaryH unaryK
    cases NatUnaryPrefix_trichotomy_hsame_strict unaryH unaryK with
    | inl sameHK =>
        exact
          ⟨OrderUnaryComparisonCarrier.mk h k unaryH unaryK
            (OrderComparisonBranch.same sameHK), rfl, rfl⟩
    | inr strictCases =>
        cases strictCases with
        | inl leftStrict =>
            exact
              ⟨OrderUnaryComparisonCarrier.mk h k unaryH unaryK
                (OrderComparisonBranch.leftPrefix leftStrict), rfl, rfl⟩
        | inr rightStrict =>
            exact
              ⟨OrderUnaryComparisonCarrier.mk h k unaryH unaryK
                (OrderComparisonBranch.rightPrefix rightStrict), rfl, rfl⟩

theorem OrderEndpointTransportObligation {Z : OrderUnaryComparisonCarrier}
    {left right : BHist} :
    hsame Z.left left → hsame Z.right right →
      UnaryHistory left ∧ UnaryHistory right ∧
        (NatUnaryStrictPrefix left right ∨
          NatUnaryStrictPrefix right left ∨ hsame left right) := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory NatUnaryStrictPrefix
  intro leftSame rightSame
  have leftUnary : UnaryHistory left :=
    unary_transport Z.leftUnary leftSame
  have rightUnary : UnaryHistory right :=
    unary_transport Z.rightUnary rightSame
  have branch :
      NatUnaryStrictPrefix left right ∨
        NatUnaryStrictPrefix right left ∨ hsame left right := by
    cases Z.branch with
    | leftPrefix strict =>
        cases strict with
        | intro tail data =>
            exact Or.inl
              (NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
                data.right.right leftSame rightSame)
    | rightPrefix strict =>
        cases strict with
        | intro tail data =>
            exact Or.inr
              (Or.inl
                (NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
                  data.right.right rightSame leftSame))
    | same sameEndpoints =>
        exact Or.inr (Or.inr (hsame_trans (hsame_symm leftSame)
          (hsame_trans sameEndpoints rightSame)))
  exact ⟨leftUnary, rightUnary, branch⟩

theorem OrderUp_StdBridge :
    (∀ Z : OrderUnaryComparisonCarrier,
      UnaryHistory Z.left ∧ UnaryHistory Z.right ∧
        (NatUnaryStrictPrefix Z.left Z.right ∨
          NatUnaryStrictPrefix Z.right Z.left ∨ hsame Z.left Z.right)) ∧
      (∀ {Z : OrderUnaryComparisonCarrier} {left right : BHist},
        hsame Z.left left → hsame Z.right right →
          UnaryHistory left ∧ UnaryHistory right ∧
            (NatUnaryStrictPrefix left right ∨
              NatUnaryStrictPrefix right left ∨ hsame left right)) := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory NatUnaryStrictPrefix
  exact ⟨OrderFullNatArithmeticHandoff.left, OrderEndpointTransportObligation⟩

end BEDC.Derived.OrderUp
