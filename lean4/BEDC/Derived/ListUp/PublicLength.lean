import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.Length

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def FramedListPublicLength (A : BHist → Prop) (h : BHist) (n : Nat) : Prop :=
  ∃ xs : ListCarrier BHist, FramedListSpineRep A h xs ∧ xs.length = n

theorem FramedListPublicLength_constructor_endpoint_readback {A : BHist → Prop}
    {h : BHist} {n : Nat} :
    (FramedListPublicLength A h 0 ↔ hsame h (BHist.e0 BHist.Empty)) ∧
      (FramedListPublicLength A h (Nat.succ n) →
        ∃ a : BHist, ∃ xs : ListCarrier BHist,
          A a ∧ FramedListSpineRep A h (a :: xs) ∧
            FramedListPublicLength A (FramedListEndpoint xs) n) := by
  constructor
  · constructor
    · intro publicLength
      cases publicLength with
      | intro xs data =>
          cases data with
          | intro rep lengthEq =>
              cases xs with
              | nil =>
                  exact rep.right
              | cons _ _ =>
                  cases lengthEq
    · intro sameEndpoint
      exact Exists.intro []
        (And.intro
          (And.intro
            (fun x mem => by
              cases mem)
            sameEndpoint)
          rfl)
  · intro publicLength
    cases publicLength with
    | intro xs data =>
        cases data with
        | intro rep lengthEq =>
            cases xs with
            | nil =>
                cases lengthEq
            | cons a tail =>
                have tailLength : tail.length = n :=
                  Nat.succ.inj lengthEq
                have tailEntries : ∀ x : BHist, x ∈ tail → A x := by
                  intro x mem
                  exact rep.left x (List.Mem.tail a mem)
                have tailPublic : FramedListPublicLength A (FramedListEndpoint tail) n :=
                  Exists.intro tail
                    (And.intro
                      (And.intro tailEntries (hsame_refl (FramedListEndpoint tail)))
                      tailLength)
                exact Exists.intro a
                  (Exists.intro tail
                    (And.intro
                      (rep.left a (List.Mem.head tail))
                      (And.intro rep tailPublic)))

theorem FramedListPublicLength_successor_empty_absurd {A : BHist -> Prop}
    {h : BHist} {n : Nat} :
    FramedListPublicLength A h (Nat.succ n) -> hsame h (BHist.e0 BHist.Empty) ->
      False := by
  intro publicLength sameEmpty
  have readback :=
    FramedListPublicLength_constructor_endpoint_readback
      (A := A) (h := h) (n := n) |>.right publicLength
  cases readback with
  | intro a rest =>
      cases rest with
      | intro xs data =>
          have sameCons : hsame (FramedListEndpoint (a :: xs)) (FramedListEndpoint []) :=
            hsame_trans (hsame_symm data.right.left.right) sameEmpty
          exact
            (FramedListEndpoint_no_confusion_cons_inversion
              (a := a) (b := a) (xs := xs) (ys := xs)).right.left sameCons

theorem FramedListHistoryCarrier_public_length_shape_exhaustion {A : BHist → Prop}
    {h : BHist} :
    FramedListHistoryCarrier A h →
      (FramedListPublicLength A h 0 ∧ hsame h (BHist.e0 BHist.Empty)) ∨
        ∃ a : BHist, ∃ xs : ListCarrier BHist,
          A a ∧ FramedListSpineRep A h (a :: xs) ∧
            FramedListPublicLength A (FramedListEndpoint xs) xs.length ∧
              hsame h (BHist.e1 (PairFrame a (FramedListEndpoint xs))) := by
  intro carrier
  cases carrier with
  | intro xs rep =>
      cases xs with
      | nil =>
          exact Or.inl
            (And.intro
              (Exists.intro []
                (And.intro rep rfl))
              rep.right)
      | cons a xs =>
          have sourceA : A a :=
            rep.left a (List.Mem.head xs)
          have tailRep : FramedListSpineRep A (FramedListEndpoint xs) xs := by
            constructor
            · intro z memZ
              exact rep.left z (List.Mem.tail a memZ)
            · exact hsame_refl (FramedListEndpoint xs)
          have tailPublic : FramedListPublicLength A (FramedListEndpoint xs) xs.length :=
            Exists.intro xs (And.intro tailRep rfl)
          exact Or.inr
            (Exists.intro a
              (Exists.intro xs
                (And.intro sourceA
                  (And.intro rep
                    (And.intro tailPublic rep.right)))))

theorem FramedListPublicLength_well_defined {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (compat : ListSourceHsameCompatible A Rel) :
    (∀ {h : BHist} {n m : Nat},
      FramedListPublicLength A h n → FramedListPublicLength A h m → n = m) ∧
      (∀ {h k : BHist} {n : Nat},
        FramedListBridgeClassifier A Rel h k →
          FramedListPublicLength A h n → FramedListPublicLength A k n) := by
  constructor
  · intro h n m publicN publicM
    cases publicN with
    | intro xs dataN =>
        cases dataN with
        | intro repX lengthX =>
            cases publicM with
            | intro ys dataM =>
                cases dataM with
                | intro repY lengthY =>
                    have sameLength : xs.length = ys.length :=
                      FramedListSpineRep_length_determinism compat repX repY
                    exact Eq.trans (Eq.symm lengthX) (Eq.trans sameLength lengthY)
  · intro h k n bridge publicN
    cases publicN with
    | intro xs0 dataN =>
        cases dataN with
        | intro repH0 lengthX0 =>
            cases bridge with
            | intro xs bridgeTail =>
                cases bridgeTail with
                | intro ys bridgeData =>
                    cases bridgeData with
                    | intro _repH bridgeRest =>
                        cases bridgeRest with
                        | intro repK _classified =>
                            have sameLength : xs0.length = ys.length :=
                              FramedListBridgeClassifier_represented_length compat repH0
                                repK
                                (Exists.intro xs
                                  (Exists.intro ys
                                    (And.intro _repH (And.intro repK _classified))))
                            exact Exists.intro ys
                              (And.intro repK (Eq.trans (Eq.symm sameLength) lengthX0))

theorem FramedListPublicLength_successor_endpoint_readback {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (compat : ListSourceHsameCompatible A Rel)
    {h : BHist} {n : Nat} :
    FramedListPublicLength A h (Nat.succ n) ->
      ∃ a : BHist, ∃ xs : ListCarrier BHist,
        A a ∧ FramedListSpineRep A h (a :: xs) ∧ xs.length = n ∧
          hsame h (BHist.e1 (PairFrame a (FramedListEndpoint xs))) := by
  intro publicLength
  have readback :=
    FramedListPublicLength_constructor_endpoint_readback
      (A := A) (h := h) (n := n) |>.right publicLength
  cases readback with
  | intro a tail =>
      cases tail with
      | intro xs data =>
          have tailEntries : ∀ z : BHist, z ∈ xs -> A z := by
            intro z memZ
            exact data.right.left.left z (List.Mem.tail a memZ)
          have canonicalTailPublic :
              FramedListPublicLength A (FramedListEndpoint xs) xs.length :=
            Exists.intro xs
              (And.intro
                (And.intro tailEntries (hsame_refl (FramedListEndpoint xs)))
                rfl)
          have tailLength : xs.length = n :=
            (FramedListPublicLength_well_defined
              (A := A) (Rel := Rel) compat).left canonicalTailPublic data.right.right
          exact Exists.intro a
            (Exists.intro xs
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro tailLength data.right.left.right))))

theorem FramedListBridgeClassifier_public_successor_component_exactness
    {A : BHist → Prop} {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    (FramedListBridgeClassifier A Rel h k ∧
      FramedListPublicLength A h (Nat.succ n) ∧
      FramedListPublicLength A k (Nat.succ n)) ↔
      ∃ a b : BHist, ∃ xs ys : ListCarrier BHist,
        A a ∧ A b ∧ FramedListSpineRep A h (a :: xs) ∧
        FramedListSpineRep A k (b :: ys) ∧
        FramedListPublicLength A (FramedListEndpoint xs) n ∧
        FramedListPublicLength A (FramedListEndpoint ys) n ∧
        Rel a b ∧ ListClassifierSpec Rel xs ys := by
  constructor
  · intro publicBridge
    have readH :=
      (FramedListPublicLength_constructor_endpoint_readback
        (A := A) (h := h) (n := n)).right publicBridge.right.left
    have readK :=
      (FramedListPublicLength_constructor_endpoint_readback
        (A := A) (h := k) (n := n)).right publicBridge.right.right
    cases readH with
    | intro a readHTail =>
        cases readHTail with
        | intro xs readHData =>
            cases readHData with
            | intro sourceA readHRest =>
                cases readHRest with
                | intro repH tailPublicH =>
                    cases readK with
                    | intro b readKTail =>
                        cases readKTail with
                        | intro ys readKData =>
                            cases readKData with
                            | intro sourceB readKRest =>
                                cases readKRest with
                                | intro repK tailPublicK =>
                                    have componentClassified :
                                        Rel a b ∧ ListClassifierSpec Rel xs ys :=
                                      (FramedListBridgeClassifier_constructor_exactness
                                        cert compat).right.right.right repH repK |>.mp
                                        publicBridge.left
                                    exact Exists.intro a
                                      (Exists.intro b
                                        (Exists.intro xs
                                          (Exists.intro ys
                                            (And.intro sourceA
                                              (And.intro sourceB
                                                (And.intro repH
                                                  (And.intro repK
                                                    (And.intro tailPublicH
                                                      (And.intro tailPublicK
                                                        componentClassified)))))))))
  · intro componentData
    cases componentData with
    | intro a restA =>
        cases restA with
        | intro b restB =>
            cases restB with
            | intro xs restXS =>
                cases restXS with
                | intro ys data =>
                    cases data with
                    | intro sourceA data =>
                        cases data with
                        | intro sourceB data =>
                            cases data with
                            | intro repH data =>
                                cases data with
                                | intro repK data =>
                                    cases data with
                                    | intro tailPublicH data =>
                                        cases data with
                                        | intro tailPublicK componentClassified =>
                                            have bridge : FramedListBridgeClassifier A Rel h k :=
                                              (FramedListBridgeClassifier_constructor_exactness
                                                cert compat).right.right.right repH repK |>.mpr
                                                componentClassified
                                            have tailEntriesH :
                                                ∀ z : BHist, z ∈ xs → A z := by
                                              intro z mem
                                              exact repH.left z (List.Mem.tail a mem)
                                            have canonicalTailPublicH :
                                                FramedListPublicLength A
                                                  (FramedListEndpoint xs) xs.length :=
                                              Exists.intro xs
                                                (And.intro
                                                  (And.intro tailEntriesH
                                                    (hsame_refl (FramedListEndpoint xs)))
                                                  rfl)
                                            have tailLengthH : xs.length = n :=
                                              (FramedListPublicLength_well_defined
                                                (A := A) (Rel := Rel) compat).left
                                                canonicalTailPublicH tailPublicH
                                            have publicH :
                                                FramedListPublicLength A h (Nat.succ n) :=
                                              Exists.intro (a :: xs)
                                                (And.intro repH (congrArg Nat.succ tailLengthH))
                                            have tailEntriesK :
                                                ∀ z : BHist, z ∈ ys → A z := by
                                              intro z mem
                                              exact repK.left z (List.Mem.tail b mem)
                                            have canonicalTailPublicK :
                                                FramedListPublicLength A
                                                  (FramedListEndpoint ys) ys.length :=
                                              Exists.intro ys
                                                (And.intro
                                                  (And.intro tailEntriesK
                                                    (hsame_refl (FramedListEndpoint ys)))
                                                  rfl)
                                            have tailLengthK : ys.length = n :=
                                              (FramedListPublicLength_well_defined
                                                (A := A) (Rel := Rel) compat).left
                                                canonicalTailPublicK tailPublicK
                                            have publicK :
                                                FramedListPublicLength A k (Nat.succ n) :=
                                              Exists.intro (b :: ys)
                                                (And.intro repK (congrArg Nat.succ tailLengthK))
                                            exact And.intro bridge (And.intro publicH publicK)

theorem FramedListBridgeClassifier_public_successor_endpoint_nonempty
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    FramedListBridgeClassifier A Rel h k -> FramedListPublicLength A h (Nat.succ n) ->
      FramedListPublicLength A k (Nat.succ n) ->
        (hsame h BHist.Empty -> False) ∧ (hsame k BHist.Empty -> False) := by
  intro bridge publicH publicK
  have components :=
    (FramedListBridgeClassifier_public_successor_component_exactness
      (A := A) (Rel := Rel) cert compat).mp
      (And.intro bridge (And.intro publicH publicK))
  cases components with
  | intro a restA =>
      cases restA with
      | intro b restB =>
          cases restB with
          | intro xs restXS =>
              cases restXS with
              | intro ys data =>
                  cases data with
                  | intro _sourceA data =>
                      cases data with
                      | intro _sourceB data =>
                          cases data with
                          | intro repH data =>
                              cases data with
                              | intro repK _rest =>
                                  constructor
                                  · intro sameHEmpty
                                    have endpointEmpty :
                                        hsame (FramedListEndpoint (a :: xs)) BHist.Empty :=
                                      hsame_trans (hsame_symm repH.right) sameHEmpty
                                    exact not_hsame_e1_empty endpointEmpty
                                  · intro sameKEmpty
                                    have endpointEmpty :
                                        hsame (FramedListEndpoint (b :: ys)) BHist.Empty :=
                                      hsame_trans (hsame_symm repK.right) sameKEmpty
                                    exact not_hsame_e1_empty endpointEmpty

theorem FramedListBridgeClassifier_successor_component_exactness_iff
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    (FramedListBridgeClassifier A Rel h k ∧ FramedListPublicLength A h (Nat.succ n) ∧
      FramedListPublicLength A k (Nat.succ n)) ↔
      ∃ a b : BHist, ∃ xs ys : ListCarrier BHist,
        A a ∧ A b ∧ FramedListSpineRep A h (a :: xs) ∧
          FramedListSpineRep A k (b :: ys) ∧
            FramedListPublicLength A (FramedListEndpoint xs) n ∧
              FramedListPublicLength A (FramedListEndpoint ys) n ∧ Rel a b ∧
                FramedListBridgeClassifier A Rel (FramedListEndpoint xs)
                  (FramedListEndpoint ys) := by
  constructor
  · intro data
    have readH := FramedListPublicLength_constructor_endpoint_readback.right data.right.left
    have readK := FramedListPublicLength_constructor_endpoint_readback.right data.right.right
    cases readH with
    | intro a tailH =>
        cases tailH with
        | intro xs packH =>
            cases readK with
            | intro b tailK =>
                cases tailK with
                | intro ys packK =>
                    have split :=
                      ((FramedListBridgeClassifier_constructor_exactness cert compat).right.right.right
                        packH.right.left packK.right.left).mp data.left
                    have tailRepH : FramedListSpineRep A (FramedListEndpoint xs) xs := by
                      constructor
                      · intro z memZ
                        exact packH.right.left.left z (List.Mem.tail a memZ)
                      · exact hsame_refl (FramedListEndpoint xs)
                    have tailRepK : FramedListSpineRep A (FramedListEndpoint ys) ys := by
                      constructor
                      · intro z memZ
                        exact packK.right.left.left z (List.Mem.tail b memZ)
                      · exact hsame_refl (FramedListEndpoint ys)
                    have tailBridge :
                        FramedListBridgeClassifier A Rel (FramedListEndpoint xs)
                          (FramedListEndpoint ys) :=
                      (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                        tailRepH tailRepK).mpr split.right
                    exact ⟨a, b, xs, ys, packH.left, packK.left, packH.right.left,
                      packK.right.left, packH.right.right, packK.right.right,
                        split.left, tailBridge⟩
  · intro data
    cases data with
    | intro a rest =>
        cases rest with
        | intro b rest =>
            cases rest with
            | intro xs rest =>
                cases rest with
                | intro ys pack =>
                    have tailRepH : FramedListSpineRep A (FramedListEndpoint xs) xs := by
                      constructor
                      · intro z memZ
                        exact pack.right.right.left.left z (List.Mem.tail a memZ)
                      · exact hsame_refl (FramedListEndpoint xs)
                    have tailRepK : FramedListSpineRep A (FramedListEndpoint ys) ys := by
                      constructor
                      · intro z memZ
                        exact pack.right.right.right.left.left z (List.Mem.tail b memZ)
                      · exact hsame_refl (FramedListEndpoint ys)
                    have tailClassified : ListClassifierSpec Rel xs ys :=
                      (FramedListBridgeClassifier_displayed_spine_exactness cert compat
                        tailRepH tailRepK).mp pack.right.right.right.right.right.right.right
                    have bridge : FramedListBridgeClassifier A Rel h k :=
                      ((FramedListBridgeClassifier_constructor_exactness cert compat).right.right.right
                        pack.right.right.left pack.right.right.right.left).mpr
                        ⟨pack.right.right.right.right.right.right.left, tailClassified⟩
                    have publicH : FramedListPublicLength A h (Nat.succ n) := by
                      cases pack.right.right.right.right.left with
                      | intro xs0 tailPublic =>
                          have sameLength := FramedListSpineRep_length_determinism compat
                            tailRepH tailPublic.left
                          exact ⟨a :: xs,
                            pack.right.right.left,
                              congrArg Nat.succ (Eq.trans sameLength tailPublic.right)⟩
                    have publicK : FramedListPublicLength A k (Nat.succ n) := by
                      cases pack.right.right.right.right.right.left with
                      | intro ys0 tailPublic =>
                          have sameLength := FramedListSpineRep_length_determinism compat
                            tailRepK tailPublic.left
                          exact ⟨b :: ys,
                            pack.right.right.right.left,
                              congrArg Nat.succ (Eq.trans sameLength tailPublic.right)⟩
                    exact ⟨bridge, publicH, publicK⟩

theorem FramedListBridgeClassifier_public_length_total {A : BHist → Prop}
    {Rel : BHist → BHist → Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} :
    FramedListBridgeClassifier A Rel h k →
      (FramedListHistoryCarrier A h ∧ FramedListHistoryCarrier A k) ∧
        ∃ n : Nat, FramedListPublicLength A h n ∧ FramedListPublicLength A k n := by
  intro bridge
  have carriers :
      FramedListHistoryCarrier A h ∧ FramedListHistoryCarrier A k :=
    (FramedListBridgeClassifier_equivalence_fields cert compat).right.left bridge
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repH bridgeRest =>
              cases bridgeRest with
              | intro repK classified =>
                  have sameLength : xs.length = ys.length :=
                    ListClassifierSpec_length_eq classified
                  exact And.intro carriers
                    (Exists.intro xs.length
                        (And.intro
                          (Exists.intro xs (And.intro repH rfl))
                          (Exists.intro ys (And.intro repK sameLength.symm))))

theorem FramedListPublicLength_bridge_transport_pair {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} :
    FramedListBridgeClassifier A Rel h k ->
      (∀ {n : Nat}, FramedListPublicLength A h n -> FramedListPublicLength A k n) ∧
        (∀ {n : Nat}, FramedListPublicLength A k n -> FramedListPublicLength A h n) := by
  intro bridge
  have wellDefined := FramedListPublicLength_well_defined (A := A) (Rel := Rel) compat
  have symmetry :=
    (FramedListBridgeClassifier_equivalence_fields cert compat).right.right.left bridge
  constructor
  · intro n publicH
    exact wellDefined.right bridge publicH
  · intro n publicK
    exact wellDefined.right symmetry publicK

theorem FramedListBridgeClassifier_public_length_transport {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    FramedListBridgeClassifier A Rel h k ->
      (FramedListPublicLength A h n -> FramedListPublicLength A k n) /\
        (FramedListPublicLength A k n -> FramedListPublicLength A h n) := by
  intro bridge
  have reverseBridge : FramedListBridgeClassifier A Rel k h :=
    (FramedListBridgeClassifier_equivalence_fields cert compat).right.right.left bridge
  constructor
  · exact (FramedListPublicLength_well_defined compat).right bridge
  · exact (FramedListPublicLength_well_defined compat).right reverseBridge

theorem FramedListPublicLength_classifier_transport {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} {n : Nat} :
    FramedListBridgeClassifier A Rel h k ->
      (FramedListPublicLength A h n -> FramedListPublicLength A k n) ∧
        (FramedListPublicLength A k n -> FramedListPublicLength A h n) := by
  intro bridge
  have forward :
      FramedListPublicLength A h n -> FramedListPublicLength A k n :=
    (FramedListPublicLength_well_defined compat).right bridge
  have bridgeSymm : FramedListBridgeClassifier A Rel k h :=
    (FramedListBridgeClassifier_equivalence_fields cert compat).right.right.left bridge
  have backward :
      FramedListPublicLength A k n -> FramedListPublicLength A h n :=
    (FramedListPublicLength_well_defined compat).right bridgeSymm
  exact And.intro forward backward

end BEDC.Derived.ListUp
