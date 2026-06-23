import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopLocatedConvexHullUp : Type where
  | mk (R M C K P A W D Q H T S N : BHist) : BishopLocatedConvexHullUp

end BEDC.Derived
