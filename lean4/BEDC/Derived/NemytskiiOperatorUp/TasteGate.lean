import BEDC.Derived.NemytskiiOperatorUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.NemytskiiOperatorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def NemytskiiOperatorCarrier (D M F W I T S R H C P N : BHist) : Prop :=
  UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory F ∧ UnaryHistory W ∧
    UnaryHistory I ∧ UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory R ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N

theorem NemytskiiOperatorNamecertObligations
    {D M F W I T S R H C P N kernelRead targetRead : BHist} :
    NemytskiiOperatorCarrier D M F W I T S R H C P N ->
      Cont M F kernelRead ->
        Cont kernelRead T targetRead ->
          SemanticNameCert
              (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row D ∨ hsame row M ∨ hsame row F ∨ hsame row W ∨ hsame row I ∨
                  hsame row T ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                      hsame row kernelRead ∨ hsame row targetRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M F kernelRead ∧ Cont kernelRead T targetRead)
              hsame ∧ UnaryHistory kernelRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier kernelRoute targetRoute
  obtain ⟨unaryD, unaryM, unaryF, _unaryW, _unaryI, unaryT, _unaryS, _unaryR,
    _unaryH, _unaryC, _unaryP, _unaryN⟩ := carrier
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed unaryM unaryF kernelRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed kernelUnary unaryT targetRoute
  have sourceAtTarget : hsame targetRead targetRead ∧ UnaryHistory targetRead :=
    ⟨hsame_refl targetRead, targetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row F ∨ hsame row W ∨ hsame row I ∨
              hsame row T ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row kernelRead ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M F kernelRead ∧ Cont kernelRead T targetRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead sourceAtTarget
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      have sameTarget : hsame row targetRead := source.left
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameTarget))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, kernelRoute, targetRoute⟩
  }
  exact ⟨cert, kernelUnary, targetUnary⟩

theorem NemytskiiOperatorMeasurableHandoff
    {D M F W I T S R H C P N witnessRead measurableRead : BHist} :
    NemytskiiOperatorCarrier D M F W I T S R H C P N ->
      Cont F W witnessRead ->
        Cont witnessRead I measurableRead ->
          UnaryHistory F ∧ UnaryHistory W ∧ UnaryHistory I ∧ UnaryHistory witnessRead ∧
            UnaryHistory measurableRead ∧ Cont F W witnessRead ∧
              Cont witnessRead I measurableRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier witnessRoute measurableRoute
  obtain ⟨_unaryD, _unaryM, unaryF, unaryW, unaryI, _unaryT, _unaryS, _unaryR,
    _unaryH, _unaryC, _unaryP, _unaryN⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed unaryF unaryW witnessRoute
  have measurableUnary : UnaryHistory measurableRead :=
    unary_cont_closed witnessUnary unaryI measurableRoute
  exact
    ⟨unaryF, unaryW, unaryI, witnessUnary, measurableUnary, witnessRoute,
      measurableRoute⟩

end BEDC.Derived.NemytskiiOperatorUp
