import BEDC.Derived.IshiharaTrickUp

namespace BEDC.Derived.IshiharaTrickUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IshiharaTrickSpeckerBoundaryHandoff [AskSetup] [PackageSetup]
    {S R T W D E A H C P N scheduleRead windowRead boundaryRead sealRead
      obstructionRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IshiharaTrickCarrier S R T W D E A H C P N bundle pkg →
      Cont S R scheduleRead →
        Cont scheduleRead W windowRead →
          Cont windowRead D boundaryRead →
            Cont boundaryRead E sealRead →
              Cont sealRead A obstructionRead →
                PkgSig bundle obstructionRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row R ∨ hsame row T ∨ hsame row W ∨
                          hsame row D ∨ hsame row E ∨ hsame row A ∨
                            hsame row obstructionRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S R scheduleRead ∧
                          Cont scheduleRead W windowRead ∧ Cont windowRead D boundaryRead ∧
                            Cont boundaryRead E sealRead ∧ Cont sealRead A obstructionRead ∧
                              PkgSig bundle obstructionRead pkg)
                      hsame ∧
                    UnaryHistory obstructionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier scheduleRoute windowRoute boundaryRoute sealRoute obstructionRoute
    obstructionPkg
  obtain ⟨unaryS, unaryR, _unaryT, unaryW, unaryD, unaryE, unaryA, _unaryH, _unaryC,
    _unaryP, _unaryN, _carrierSchedule, _carrierWindowBoundary, _carrierTest,
    _carrierReplay, _carrierPkg, _carrierNamePkg⟩ := carrier
  have unarySchedule : UnaryHistory scheduleRead :=
    unary_cont_closed unaryS unaryR scheduleRoute
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unarySchedule unaryW windowRoute
  have unaryBoundary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryWindow unaryD boundaryRoute
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryBoundary unaryE sealRoute
  have unaryObstruction : UnaryHistory obstructionRead :=
    unary_cont_closed unarySeal unaryA obstructionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obstructionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row T ∨ hsame row W ∨ hsame row D ∨
              hsame row E ∨ hsame row A ∨ hsame row obstructionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R scheduleRead ∧ Cont scheduleRead W windowRead ∧
              Cont windowRead D boundaryRead ∧ Cont boundaryRead E sealRead ∧
                Cont sealRead A obstructionRead ∧ PkgSig bundle obstructionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obstructionRead ⟨hsame_refl obstructionRead, unaryObstruction⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, scheduleRoute, windowRoute, boundaryRoute, sealRoute,
          obstructionRoute, obstructionPkg⟩
  }
  exact ⟨cert, unaryObstruction⟩

end BEDC.Derived.IshiharaTrickUp
