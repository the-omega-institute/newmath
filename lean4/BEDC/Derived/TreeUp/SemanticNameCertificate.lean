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

end BEDC.Derived.TreeUp
