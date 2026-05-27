import BEDC.Derived.RiemannIntegralUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RiemannIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannIntegralCarrier_darboux_step_scope [AskSetup] [PackageSetup]
    {M T F S D G R H C P N tagRead sumRead darbouxRead gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannIntegralPacket M T F S D G R H C N P bundle pkg ->
      Cont M T tagRead ->
        Cont F S sumRead ->
          Cont sumRead D darbouxRead ->
            Cont darbouxRead G gapRead ->
              PkgSig bundle gapRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row T ∨ hsame row S ∨ hsame row D ∨
                        hsame row G ∨ Cont darbouxRead G gapRead)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle gapRead pkg ∧
                        hsame row gapRead)
                    hsame ∧
                  UnaryHistory tagRead ∧ UnaryHistory sumRead ∧
                    UnaryHistory darbouxRead ∧ UnaryHistory gapRead ∧
                      Cont M T tagRead ∧ Cont F S sumRead ∧
                        Cont sumRead D darbouxRead ∧ Cont darbouxRead G gapRead ∧
                          PkgSig bundle gapRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier tagRoute sumRoute darbouxRoute gapRoute gapPkg
  obtain ⟨mUnary, tUnary, fUnary, sUnary, dUnary, gUnary, _rUnary, _hUnary,
    _cUnary, _nUnary, _pUnary, _mtf, _fsd, _dgr, provenancePkg⟩ := carrier
  have tagUnary : UnaryHistory tagRead :=
    unary_cont_closed mUnary tUnary tagRoute
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed fUnary sUnary sumRoute
  have darbouxUnary : UnaryHistory darbouxRead :=
    unary_cont_closed sumUnary dUnary darbouxRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed darbouxUnary gUnary gapRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row S ∨ hsame row D ∨ hsame row G ∨
              Cont darbouxRead G gapRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle gapRead pkg ∧ hsame row gapRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro gapRead
          ⟨hsame_refl gapRead, gapUnary⟩
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
          intro row other sameRows source
          have otherSame : hsame other gapRead :=
            hsame_trans (hsame_symm sameRows) source.left
          have otherUnary : UnaryHistory other :=
            unary_transport source.right sameRows
          exact ⟨otherSame, otherUnary⟩
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr gapRoute))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, gapPkg, source.left⟩
    }
  exact
    ⟨cert, tagUnary, sumUnary, darbouxUnary, gapUnary, tagRoute, sumRoute, darbouxRoute,
      gapRoute, gapPkg⟩

end BEDC.Derived.RiemannIntegralUp
