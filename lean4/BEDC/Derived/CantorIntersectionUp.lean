import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CantorIntersectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive CantorIntersectionCarrier where
  | packet
      (nestedIntersection widthWindow diagonalSelector endpointEnclosure regSeqRatHandoff
        realSeal transport package nameCert : BHist) :
      CantorIntersectionCarrier

structure CantorIntersectionCarrier_namecert_obligations where
  carrier : CantorIntersectionCarrier -> Prop
  finiteWindowClassifier : CantorIntersectionCarrier -> CantorIntersectionCarrier -> Prop
  selectorStability : CantorIntersectionCarrier -> CantorIntersectionCarrier -> Prop
  regSeqRatHandoffExactness : CantorIntersectionCarrier -> Prop
  realSealNonescape : CantorIntersectionCarrier -> Prop

theorem CantorIntersectionCarrier_namecert_obligation_surface :
    ∃ cert : CantorIntersectionCarrier_namecert_obligations,
      ∀ x : CantorIntersectionCarrier, cert.carrier x ->
        ∃ N W D E R H C P Q : BHist,
          x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
            cert.regSeqRatHandoffExactness x ∧ cert.realSealNonescape x := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  let cert : CantorIntersectionCarrier_namecert_obligations :=
    { carrier := fun x =>
        ∃ N W D E R H C P Q : BHist, x = CantorIntersectionCarrier.packet N W D E R H C P Q
      finiteWindowClassifier := fun x y =>
        ∃ N W D E R H C P Q N' W' D' E' R' H' C' P' Q' : BHist,
          x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
            y = CantorIntersectionCarrier.packet N' W' D' E' R' H' C' P' Q' ∧
              hsame N N' ∧ hsame W W' ∧ hsame D D' ∧ hsame E E' ∧
                hsame R R' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame Q Q'
      selectorStability := fun x y =>
        ∃ N W D E R H C P Q N' W' D' E' R' H' C' P' Q' selected selected' : BHist,
          x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
            y = CantorIntersectionCarrier.packet N' W' D' E' R' H' C' P' Q' ∧
              Cont N W selected ∧ Cont N' W' selected' ∧ hsame selected selected'
      regSeqRatHandoffExactness := fun x =>
        ∃ N W D E R H C P Q endpointRead regularRead : BHist,
          x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
            Cont D E endpointRead ∧
              Cont endpointRead R regularRead ∧ hsame regularRead (append endpointRead R)
      realSealNonescape := fun x =>
        ∃ N W D E R H C P Q regularRead realRead visibleRoute : BHist,
          x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
            Cont E R regularRead ∧
              Cont regularRead H realRead ∧
                Cont (append N W) (append D E) visibleRoute ∧
                  hsame realRead (append regularRead H) }
  exact ⟨cert, by
    intro x hcarrier
    cases hcarrier with
    | intro N hcarrier =>
        cases hcarrier with
        | intro W hcarrier =>
            cases hcarrier with
            | intro D hcarrier =>
                cases hcarrier with
                | intro E hcarrier =>
                    cases hcarrier with
                    | intro R hcarrier =>
                        cases hcarrier with
                        | intro H hcarrier =>
                            cases hcarrier with
                            | intro C hcarrier =>
                                cases hcarrier with
                                | intro P hcarrier =>
                                    cases hcarrier with
                                    | intro Q hx =>
                                        cases hx
                                        exact
                                          ⟨N, W, D, E, R, H, C, P, Q, rfl,
                                            ⟨N, W, D, E, R, H, C, P, Q, append D E,
                                              append (append D E) R, rfl, rfl, rfl, rfl⟩,
                                            ⟨N, W, D, E, R, H, C, P, Q, append E R,
                                              append (append E R) H, append (append N W) (append D E),
                                              rfl, rfl, rfl, rfl, rfl⟩⟩⟩

theorem CantorIntersectionRealSealNonescape (x : CantorIntersectionCarrier) :
    ∃ N W D E R H C P Q selectedWindow selectedEndpoint regSeqRead realRead replay : BHist,
      x = CantorIntersectionCarrier.packet N W D E R H C P Q ∧
        Cont W D selectedWindow ∧
          Cont selectedWindow E selectedEndpoint ∧
            Cont selectedEndpoint R regSeqRead ∧
              Cont regSeqRead H realRead ∧
                Cont C P replay ∧ hsame realRead (append regSeqRead H) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  cases x with
  | packet N W D E R H C P Q =>
      exact
        ⟨N, W, D, E, R, H, C, P, Q,
          append W D,
          append (append W D) E,
          append (append (append W D) E) R,
          append (append (append (append W D) E) R) H,
          append C P,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem CantorIntersectionDyadicIntervalBasisBridge
    {N W D E R H C P Q basisCell regularRead realRead : BHist} :
    Cont D E basisCell ->
      Cont basisCell R regularRead ->
        Cont regularRead H realRead ->
          SemanticNameCert
            (fun row : BHist =>
              hsame row realRead ∧
                ∃ x : CantorIntersectionCarrier,
                  x = CantorIntersectionCarrier.packet N W D E R H C P Q)
            (fun _row : BHist =>
              Cont D E basisCell ∧
                Cont basisCell R regularRead ∧ Cont regularRead H realRead)
            (fun row : BHist => hsame row realRead)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro hDE hBasisR hRegularH
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · exact
      ⟨realRead, And.intro rfl
        ⟨CantorIntersectionCarrier.packet N W D E R H C P Q, rfl⟩⟩
  · intro h _source
    exact hsame_refl h
  · intro h k hsameHK
    exact hsame_symm hsameHK
  · intro h k r hsameHK hsameKR
    exact hsame_trans hsameHK hsameKR
  · intro h k hsameHK sourceH
    cases hsameHK
    exact sourceH
  · intro _row _source
    exact And.intro hDE (And.intro hBasisR hRegularH)
  · intro _row source
    exact source.left

end BEDC.Derived.CantorIntersectionUp
