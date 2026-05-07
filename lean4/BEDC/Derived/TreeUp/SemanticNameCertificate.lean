import BEDC.Derived.TreeUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

theorem TreeBHistCarrier_semantic_name_certificate
    {graph edge connected acyclic root endpoint : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      SemanticNameCert
        (fun h : BHist => TreeBHistCarrier graph edge connected acyclic root h)
        (fun h : BHist => TreeBHistCarrier graph edge connected acyclic root h)
        (fun h : BHist => TreeBHistCarrier graph edge connected acyclic root h)
        hsame := by
  intro carrier
  constructor
  · constructor
    · exact Exists.intro endpoint carrier
    · intro h _carrierH
      exact hsame_refl h
    · intro _h _k same
      exact hsame_symm same
    · intro _h _k _r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      have transportedBranch :
          TreeRootBranch k root connected ∧ UnaryHistory root ∧ Cont k root connected :=
        TreeBHistCarrier_root_branch_transport carrierH same (hsame_refl root)
          (hsame_refl connected)
      exact And.intro carrierH.left
        (And.intro carrierH.right.left transportedBranch.left)
  · intro _h source
    exact source
  · intro _h source
    exact source

theorem TreeBHistCarrier_derivation_syntax_roundtrip
    {graph edge connected acyclic root endpoint syntaxHist syntaxTarget endpoint'
      syntaxTarget' : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      UnaryHistory syntaxHist -> Cont endpoint syntaxHist syntaxTarget ->
        hsame endpoint endpoint' -> hsame syntaxTarget syntaxTarget' ->
          TreeBHistCarrier graph edge connected acyclic root endpoint' ∧
            GraphContEdge endpoint' syntaxHist syntaxTarget' ∧
              TreeRootBranch endpoint' root connected ∧ UnaryHistory syntaxTarget' := by
  intro carrier syntaxUnary syntaxRoute sameEndpoint sameSyntaxTarget
  have branch :
      TreeRootBranch endpoint' root connected ∧ UnaryHistory root ∧
        Cont endpoint' root connected :=
    TreeBHistCarrier_root_branch_transport carrier sameEndpoint (hsame_refl root)
      (hsame_refl connected)
  have syntaxRoute' : Cont endpoint' syntaxHist syntaxTarget' :=
    cont_hsame_transport sameEndpoint (hsame_refl syntaxHist) sameSyntaxTarget syntaxRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    branch.left.left.left
  have syntaxTargetUnary' : UnaryHistory syntaxTarget' :=
    unary_cont_closed endpointUnary' syntaxUnary syntaxRoute'
  exact And.intro
    (And.intro carrier.left (And.intro carrier.right.left branch.left))
    (And.intro
      (And.intro endpointUnary' (And.intro syntaxUnary syntaxRoute'))
      (And.intro branch.left syntaxTargetUnary'))

end BEDC.Derived.TreeUp
