import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafConsumerAccessTrace_face_map_stability
    {root faceRoot : BHist} {left right : List BHist} (face : BHist -> BHist) :
    hsame root faceRoot ->
      (forall row : BHist, UnaryHistory row -> UnaryHistory (face row)) ->
        SheafConsumerAccessTrace root left ->
          SheafConsumerAccessTrace root right ->
            UnaryHistory faceRoot ∧
              SheafConsumerAccessTrace faceRoot (List.map face (left ++ right)) := by
  intro sameRoot faceUnary leftTrace rightTrace
  have appended :
      UnaryHistory root ∧ SheafConsumerAccessTrace root (left ++ right) :=
    SheafConsumerAccessTrace_append_closed leftTrace rightTrace
  have faceRootUnary : UnaryHistory faceRoot :=
    unary_transport appended.left sameRoot
  have mappedRows :
      forall row : BHist, List.Mem row (List.map face (left ++ right)) -> UnaryHistory row := by
    have mappedRowsFrom :
        forall source : List BHist,
          (forall row : BHist, List.Mem row source -> UnaryHistory row) ->
            forall row : BHist, List.Mem row (List.map face source) -> UnaryHistory row := by
      intro source sourceRows
      induction source with
      | nil =>
          intro row rowMem
          cases rowMem
      | cons head tail ih =>
          intro row rowMem
          cases rowMem with
          | head =>
              exact faceUnary head (sourceRows head (List.Mem.head tail))
          | tail _ tailMem =>
              have tailRows :
                  forall row : BHist, List.Mem row tail -> UnaryHistory row := by
                intro tailRow tailRowMem
                exact sourceRows tailRow (List.Mem.tail head tailRowMem)
              exact ih tailRows row tailMem
    exact mappedRowsFrom (left ++ right) appended.right.right
  exact And.intro faceRootUnary
    (And.intro faceRootUnary mappedRows)

end BEDC.Derived.SheafUp
