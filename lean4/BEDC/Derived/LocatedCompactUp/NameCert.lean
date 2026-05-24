import BEDC.Derived.LocatedCompactUp.TasteGate

namespace BEDC.Derived.LocatedCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

def LocatedCompactObligationSurface (x : LocatedCompactUp) : Prop :=
  ∃ carrier locatedness finiteNet apartness transport continuation provenance nameCert : BHist,
    x =
        LocatedCompactUp.mk carrier locatedness finiteNet apartness transport continuation
          provenance nameCert ∧
      hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist carrier)) carrier ∧
        hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist locatedness)) locatedness ∧
          hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist finiteNet)) finiteNet ∧
            hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist nameCert)) nameCert

theorem LocatedCompactNameCertObligations :
    forall x : LocatedCompactUp, LocatedCompactObligationSurface x := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  intro x
  cases x with
  | mk carrier locatedness finiteNet apartness transport continuation provenance nameCert =>
      refine
        ⟨carrier, locatedness, finiteNet, apartness, transport, continuation, provenance,
          nameCert, rfl, ?_, ?_, ?_, ?_⟩
      · change locatedCompactDecodeBHist (locatedCompactEncodeBHist carrier) = carrier
        induction carrier with
        | Empty => rfl
        | e0 carrier ih => exact congrArg BHist.e0 ih
        | e1 carrier ih => exact congrArg BHist.e1 ih
      · change locatedCompactDecodeBHist (locatedCompactEncodeBHist locatedness) = locatedness
        induction locatedness with
        | Empty => rfl
        | e0 locatedness ih => exact congrArg BHist.e0 ih
        | e1 locatedness ih => exact congrArg BHist.e1 ih
      · change locatedCompactDecodeBHist (locatedCompactEncodeBHist finiteNet) = finiteNet
        induction finiteNet with
        | Empty => rfl
        | e0 finiteNet ih => exact congrArg BHist.e0 ih
        | e1 finiteNet ih => exact congrArg BHist.e1 ih
      · change locatedCompactDecodeBHist (locatedCompactEncodeBHist nameCert) = nameCert
        induction nameCert with
        | Empty => rfl
        | e0 nameCert ih => exact congrArg BHist.e0 ih
        | e1 nameCert ih => exact congrArg BHist.e1 ih

theorem LocatedCompactFiniteNet_rows_from_obligation_surface (x : LocatedCompactUp) :
    LocatedCompactObligationSurface x →
      ∃ carrier locatedness finiteNet apartness transport continuation provenance
          nameCert : BHist,
        x =
            LocatedCompactUp.mk carrier locatedness finiteNet apartness transport
              continuation provenance nameCert ∧
          hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist locatedness))
            locatedness ∧
            hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist finiteNet))
              finiteNet := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  intro surface
  obtain
    ⟨carrier, locatedness, finiteNet, apartness, transport, continuation, provenance,
      nameCert, hx, _carrierRow, locatednessRow, finiteNetRow, _nameCertRow⟩ := surface
  exact
    ⟨carrier, locatedness, finiteNet, apartness, transport, continuation, provenance,
      nameCert, hx, locatednessRow, finiteNetRow⟩

theorem LocatedCompactCarrier_real_window_handoff (x : LocatedCompactUp) :
    ∃ carrier locatedness finiteNet apartness transport continuation provenance
        nameCert : BHist,
      x =
          LocatedCompactUp.mk carrier locatedness finiteNet apartness transport
            continuation provenance nameCert ∧
        locatedCompactToEventFlow x =
          [[BMark.b0],
            locatedCompactEncodeBHist carrier,
            [BMark.b1, BMark.b0],
            locatedCompactEncodeBHist locatedness,
            [BMark.b1, BMark.b1, BMark.b0],
            locatedCompactEncodeBHist finiteNet,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            locatedCompactEncodeBHist apartness,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            locatedCompactEncodeBHist transport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            locatedCompactEncodeBHist continuation,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            locatedCompactEncodeBHist provenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            locatedCompactEncodeBHist nameCert] ∧
          hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist finiteNet))
            finiteNet ∧
            hsame (locatedCompactDecodeBHist (locatedCompactEncodeBHist locatedness))
              locatedness ∧
              hsame
                (locatedCompactDecodeBHist (locatedCompactEncodeBHist continuation))
                continuation := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases x with
  | mk carrier locatedness finiteNet apartness transport continuation provenance nameCert =>
      refine
        ⟨carrier, locatedness, finiteNet, apartness, transport, continuation, provenance,
          nameCert, rfl, rfl, ?_, ?_, ?_⟩
      · change locatedCompactDecodeBHist (locatedCompactEncodeBHist finiteNet) = finiteNet
        induction finiteNet with
        | Empty => rfl
        | e0 finiteNet ih => exact congrArg BHist.e0 ih
        | e1 finiteNet ih => exact congrArg BHist.e1 ih
      · change
          locatedCompactDecodeBHist (locatedCompactEncodeBHist locatedness) = locatedness
        induction locatedness with
        | Empty => rfl
        | e0 locatedness ih => exact congrArg BHist.e0 ih
        | e1 locatedness ih => exact congrArg BHist.e1 ih
      · change
          locatedCompactDecodeBHist (locatedCompactEncodeBHist continuation) =
            continuation
        induction continuation with
        | Empty => rfl
        | e0 continuation ih => exact congrArg BHist.e0 ih
        | e1 continuation ih => exact congrArg BHist.e1 ih

end BEDC.Derived.LocatedCompactUp
