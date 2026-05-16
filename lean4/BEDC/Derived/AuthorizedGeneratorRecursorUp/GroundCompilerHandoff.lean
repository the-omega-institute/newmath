import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorGroundCompilerHandoff
    {signature eliminator branches transport branchRead routes publicRead : BHist} :
    Cont signature eliminator branches ->
      Cont branches transport branchRead ->
        Cont branchRead routes publicRead ->
          hsame transport BHist.Empty ->
            UnaryHistory signature ->
              UnaryHistory eliminator ->
                UnaryHistory branches ->
                  UnaryHistory routes ->
                    UnaryHistory publicRead ∧ Cont signature eliminator branches ∧
                      Cont branches transport branchRead ∧
                        Cont branchRead routes publicRead ∧ hsame transport BHist.Empty ∧
                          authorizedGeneratorRecursorEncodeBHist BHist.Empty =
                            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  intro signatureEliminatorBranches branchesTransportBranchRead branchReadRoutesPublicRead
    transportEmpty signatureUnary eliminatorUnary branchesUnary routesUnary
  have exhausted :
      UnaryHistory publicRead ∧ Cont signature eliminator branches ∧
        Cont branches transport branchRead ∧
          Cont branchRead routes publicRead ∧ hsame transport BHist.Empty :=
    AuthorizedGeneratorRecursorBranchExhaustion signatureEliminatorBranches
      branchesTransportBranchRead branchReadRoutesPublicRead transportEmpty signatureUnary
      eliminatorUnary branchesUnary routesUnary
  exact
    ⟨exhausted.left, exhausted.right.left, exhausted.right.right.left,
      exhausted.right.right.right.left, exhausted.right.right.right.right, rfl⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
