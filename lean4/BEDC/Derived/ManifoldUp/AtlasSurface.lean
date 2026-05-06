import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive ManifoldAtlasSurfaceClassifier : BHist -> BHist -> Prop where
  | atlas
      {base index domain chart transition base' index' domain' chart' transition' : BHist} :
      ManifoldAtlasPackage base index domain chart transition ->
      ManifoldAtlasPackage base' index' domain' chart' transition' ->
      ManifoldAtlasClassifier base index domain chart transition base' index' domain' chart'
        transition' ->
      ManifoldAtlasSurfaceClassifier base base'
  | symm {h k : BHist} :
      ManifoldAtlasSurfaceClassifier h k -> ManifoldAtlasSurfaceClassifier k h
  | trans {h k r : BHist} :
      ManifoldAtlasSurfaceClassifier h k -> ManifoldAtlasSurfaceClassifier k r ->
        ManifoldAtlasSurfaceClassifier h r

theorem ManifoldAtlasSurfaceClassifier_endpoints {h k : BHist} :
    ManifoldAtlasSurfaceClassifier h k ->
      (∃ index domain chart transition : BHist,
        ManifoldAtlasPackage h index domain chart transition ∧ Cont h index domain) ∧
        (∃ index domain chart transition : BHist,
          ManifoldAtlasPackage k index domain chart transition ∧ Cont k index domain) := by
  intro classified
  induction classified with
  | atlas package package' _classified =>
      constructor
      · exact Exists.intro _
          (Exists.intro _
            (Exists.intro _
              (Exists.intro _ (And.intro package package.right.right.right.right.right.left))))
      · exact Exists.intro _
          (Exists.intro _
            (Exists.intro _
              (Exists.intro _ (And.intro package' package'.right.right.right.right.right.left))))
  | symm _ endpoints =>
      exact And.intro endpoints.right endpoints.left
  | trans _ _ leftEndpoints rightEndpoints =>
      exact And.intro leftEndpoints.left rightEndpoints.right

end BEDC.Derived.ManifoldUp
