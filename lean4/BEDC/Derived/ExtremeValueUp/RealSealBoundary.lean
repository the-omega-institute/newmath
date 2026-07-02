import BEDC.Derived.ExtremeValueUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

namespace BEDC.Derived.ExtremeValueUp

theorem ExtremeValueRealSealBoundary
    {X F U M S R H C P N attainment sealRead : BHist} :
    ExtremeValuePacket X F U M S R H C P N attainment ->
      Cont S R sealRead ->
        SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row X ∨ hsame row F ∨ hsame row U ∨ hsame row M ∨
                hsame row S ∨ hsame row R ∨ hsame row sealRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont X F U ∧ Cont U M S ∧ Cont M S R ∧
                Cont S R sealRead)
            hsame ∧
          UnaryHistory sealRead ∧ Cont X F U ∧ Cont U M S ∧ Cont M S R ∧
            Cont S R sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro packet sealRoute
  obtain ⟨_xUnary, _fUnary, _uUnary, _mUnary, sUnary, rUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, sourceRoute, foldRoute, valueRoute, _attainmentRoute⟩ := packet
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sUnary rUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row U ∨ hsame row M ∨
              hsame row S ∨ hsame row R ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F U ∧ Cont U M S ∧ Cont M S R ∧
              Cont S R sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, foldRoute, valueRoute, sealRoute⟩
  }
  exact ⟨cert, sealUnary, sourceRoute, foldRoute, valueRoute, sealRoute⟩

theorem ExtremeValueFiniteNetSealBoundaryConsumer
    {X F U M S R H C P N attainment sealRead : BHist} :
    ExtremeValuePacket X F U M S R H C P N attainment ->
      Cont S R sealRead ->
        SemanticNameCert
            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row X ∨ hsame row F ∨ hsame row U ∨ hsame row M ∨
                hsame row S ∨ hsame row R ∨ hsame row sealRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont X F U ∧ Cont U M S ∧ Cont M S R ∧
                Cont S R sealRead)
            hsame ∧
          extremeValueFields (ExtremeValueUp.mk X F U M S R H C P N) =
              [X, F, U, M, S, R, H, C, P, N] ∧
            UnaryHistory U ∧ UnaryHistory S ∧ UnaryHistory sealRead ∧
              Cont X F U ∧ Cont U M S ∧ Cont S R sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro packet sealRoute
  have carrierRead :=
    BEDC.Derived.ExtremeValueUp.ExtremeValueCarrier_finite_net_attainment packet sealRoute
  have boundaryRead :=
    ExtremeValueRealSealBoundary packet sealRoute
  exact ⟨boundaryRead.left, carrierRead⟩

end BEDC.Derived.ExtremeValueUp
