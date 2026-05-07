import BEDC.Derived.GraphUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GraphUp

theorem TreeGraphSource_connected_root_path_readback
    {root endpoint step pathOut rootOut : BHist} :
    UnaryHistory root -> GraphContEdge endpoint step pathOut ->
      Cont pathOut BHist.Empty rootOut -> hsame rootOut root ->
        UnaryHistory endpoint ∧ UnaryHistory step ∧ Cont endpoint step pathOut ∧
          hsame pathOut root := by
  intro _rootUnary edge rootPath sameRoot
  have sameRootOutPath : hsame rootOut pathOut :=
    Iff.mp cont_right_unit_iff rootPath
  have samePathRoot : hsame pathOut root :=
    hsame_trans (hsame_symm sameRootOutPath) sameRoot
  exact And.intro edge.left
    (And.intro edge.right.left
      (And.intro edge.right.right samePathRoot))

end BEDC.Derived.TreeUp
