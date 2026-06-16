import BEDC.Derived.DyadicFloorUp

namespace BEDC.Derived.DyadicFloorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DyadicFloorClassifier
    (x k d s lower upper modulus readback sealRow transport replay provenance
      localName : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
    UnaryHistory k ∧ UnaryHistory d ∧ UnaryHistory s ∧ UnaryHistory lower ∧
    UnaryHistory upper ∧ UnaryHistory modulus ∧ UnaryHistory readback ∧
      Cont modulus readback lower ∧ Cont lower upper sealRow ∧ hsame x x ∧
        hsame transport transport ∧ hsame replay replay ∧ hsame provenance localName

theorem DyadicFloorClassifier_window_route
    {x k d s lower upper modulus readback sealRow transport replay provenance
      localName : BHist} :
    DyadicFloorClassifier x k d s lower upper modulus readback sealRow transport replay
        provenance localName ->
      UnaryHistory k ∧ UnaryHistory d ∧ UnaryHistory s ∧ UnaryHistory lower ∧
        UnaryHistory upper ∧ UnaryHistory modulus ∧ UnaryHistory readback ∧
          Cont modulus readback lower ∧ Cont lower upper sealRow := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro classifier
  obtain ⟨kUnary, dUnary, successorUnary, lowerUnary, upperUnary, modulusUnary,
    readbackUnary, modulusRoute, sealRoute, _requestSame, _transportSame, _replaySame,
    _provenanceSame⟩ := classifier
  exact
    ⟨kUnary, dUnary, successorUnary, lowerUnary, upperUnary, modulusUnary,
      readbackUnary, modulusRoute, sealRoute⟩

end BEDC.Derived.DyadicFloorUp
