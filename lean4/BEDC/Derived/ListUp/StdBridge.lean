import BEDC.Derived.ListUp.PublicReverseLength
import BEDC.Derived.ListUp.ReverseAppendAntimorphism

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ListUp_StdBridge {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (cert : NameCert A Rel) (compat : ListSourceHsameCompatible A Rel)
    {h k r hRev kRev s t : BHist} {n : Nat} :
    FramedListPublicAppend A h k r ->
      (exists xs : ListCarrier BHist,
        FramedListSpineRep A h xs ∧ FramedListSpineRep A hRev xs.reverse) ->
        (exists ys : ListCarrier BHist,
          FramedListSpineRep A k ys ∧ FramedListSpineRep A kRev ys.reverse) ->
          FramedListPublicAppend A kRev hRev s ->
            (exists zs : ListCarrier BHist,
              FramedListSpineRep A r zs ∧ FramedListSpineRep A t zs.reverse) ->
              FramedListPublicLength A r n ->
                FramedListBridgeClassifier A Rel s t ∧
                  FramedListPublicLength A s n ∧ FramedListPublicLength A t n := by
  intro appendHK reverseH reverseK appendRev reverseR publicR
  have bridgeST : FramedListBridgeClassifier A Rel s t :=
    FramedListPublicReverse_append_output_classifier_unique cert compat appendHK reverseH
      reverseK appendRev reverseR
  have publicT : FramedListPublicLength A t n :=
    (FramedListPublicReverse_public_length_transport cert compat reverseR).left publicR
  have publicS : FramedListPublicLength A s n :=
    (FramedListPublicLength_bridge_transport_pair cert compat bridgeST).right publicT
  exact And.intro bridgeST (And.intro publicS publicT)

end BEDC.Derived.ListUp
