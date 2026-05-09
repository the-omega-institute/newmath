import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TopGroupRootThresholdPackage_root_source_compatibility
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      ∃ sourceLedger : BHist,
        Cont (append group topology) (append product inverse) sourceLedger ∧
          UnaryHistory sourceLedger ∧
            hsame sourceLedger (append (append group topology) (append product inverse)) ∧
              Cont group topology product ∧ Cont product inverse ledger ∧
                hsame provenance ledger := by
  intro package
  let sourceLedger := append (append group topology) (append product inverse)
  have rows := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  have sourceLeftUnary : UnaryHistory (append group topology) :=
    unary_append_closed groupUnary topologyUnary
  have sourceRightUnary : UnaryHistory (append product inverse) :=
    unary_append_closed rows.right.right.left rows.right.right.right.left
  have sourceCont : Cont (append group topology) (append product inverse) sourceLedger := by
    rfl
  have sourceUnary : UnaryHistory sourceLedger :=
    unary_cont_closed sourceLeftUnary sourceRightUnary sourceCont
  exact Exists.intro sourceLedger
    (And.intro sourceCont
      (And.intro sourceUnary
        (And.intro sourceCont
          (And.intro package.right.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

end BEDC.Derived.TopGroupUp
