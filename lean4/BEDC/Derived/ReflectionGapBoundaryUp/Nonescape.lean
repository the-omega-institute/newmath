import BEDC.Derived.ReflectionGapBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReflectionGapBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ReflectionGapBoundaryCarrier (S H Sigma K P L Q T R N B : BHist) : Prop :=
  UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory Sigma ∧ UnaryHistory K ∧
    UnaryHistory P ∧ UnaryHistory L ∧ UnaryHistory Q ∧ UnaryHistory T ∧ UnaryHistory R ∧
      UnaryHistory N ∧ UnaryHistory B ∧ Cont S H Sigma ∧ Cont Sigma K P ∧
        Cont P L Q ∧ Cont Q T R ∧ Cont R B N

theorem ReflectionGapBoundary_nonescape
    {S H Sigma K P L Q T R N B publicRead : BHist} :
    ReflectionGapBoundaryCarrier S H Sigma K P L Q T R N B ->
      Cont L Q publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row publicRead ∧ Cont L Q publicRead)
            (fun row : BHist =>
              hsame row publicRead ∧ Cont L Q publicRead ∧ Cont R B N)
            hsame ∧
          UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory Sigma ∧ UnaryHistory K ∧
            UnaryHistory P ∧ UnaryHistory L ∧ UnaryHistory Q ∧ UnaryHistory T ∧
              UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory B ∧ UnaryHistory publicRead ∧
                Cont S H Sigma ∧ Cont Sigma K P ∧ Cont P L Q ∧ Cont Q T R ∧
                  Cont R B N ∧ Cont L Q publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute
  obtain ⟨unaryS, unaryH, unarySigma, unaryK, unaryP, unaryL, unaryQ, unaryT, unaryR,
    unaryN, unaryB, routeSigma, routeP, routeQ, routeR, routeN⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryL unaryQ publicRoute
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead ∧ Cont L Q publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont L Q publicRead ∧ Cont R B N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
      intro _row source
      exact ⟨source.left, publicRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicRoute, routeN⟩
  }
  exact
    ⟨cert, unaryS, unaryH, unarySigma, unaryK, unaryP, unaryL, unaryQ, unaryT, unaryR,
      unaryN, unaryB, publicUnary, routeSigma, routeP, routeQ, routeR, routeN, publicRoute⟩

end BEDC.Derived.ReflectionGapBoundaryUp
