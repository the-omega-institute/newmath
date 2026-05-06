import BEDC.Derived.LatticeUp

namespace BEDC.Derived.LatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PreorderUp

theorem LatticeUnaryPrefix_extrema_certificate {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      exists glb : BHist, exists lub : BHist,
        UnaryHistory glb ∧ UnaryHistory lub ∧
          PreorderPrefixLE glb h ∧ PreorderPrefixLE glb k ∧
          (forall {z : BHist}, UnaryHistory z -> PreorderPrefixLE z h ->
            PreorderPrefixLE z k -> PreorderPrefixLE z glb) ∧
          PreorderPrefixLE h lub ∧ PreorderPrefixLE k lub ∧
          (forall {z : BHist}, UnaryHistory z -> PreorderPrefixLE h z ->
            PreorderPrefixLE k z -> PreorderPrefixLE lub z) := by
  intro unaryH unaryK
  have total := NatUnaryPrefix_total unaryH unaryK
  cases total with
  | inl hLeK =>
      exact
        Exists.intro h
          (Exists.intro k
            (And.intro unaryH
              (And.intro unaryK
                (And.intro (PreorderPrefixLE_of_hsame (hsame_refl h))
                  (And.intro hLeK
                    (And.intro
                      (by
                        intro z _unaryZ zLeH _zLeK
                        exact zLeH)
                      (And.intro hLeK
                        (And.intro (PreorderPrefixLE_of_hsame (hsame_refl k))
                          (by
                            intro z _unaryZ _hLeZ kLeZ
                            exact kLeZ)))))))))
  | inr kLeH =>
      exact
        Exists.intro k
          (Exists.intro h
            (And.intro unaryK
              (And.intro unaryH
                (And.intro kLeH
                  (And.intro (PreorderPrefixLE_of_hsame (hsame_refl k))
                    (And.intro
                      (by
                        intro z _unaryZ _zLeH zLeK
                        exact zLeK)
                      (And.intro (PreorderPrefixLE_of_hsame (hsame_refl h))
                        (And.intro kLeH
                          (by
                            intro z _unaryZ hLeZ _kLeZ
                            exact hLeZ)))))))))

end BEDC.Derived.LatticeUp
